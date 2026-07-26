-- | A Language Server Protocol server for @.zkc@.
--
-- The point of phase 6's tooling is that the interesting thing zkc knows —
-- whether an output is determined — should reach the author where they work,
-- not only at the command line. This server publishes exactly the diagnostics
-- the CLI does, because it runs the same 'diagnoseSource' pipeline; it adds no
-- analysis of its own. It speaks LSP over JSON-RPC on stdin/stdout, framed the
-- standard way (@Content-Length@ headers), and depends on nothing but GHC's
-- boot libraries — the JSON is our own 'Zkc.Json', the framing is hand-rolled.
--
-- The protocol logic is split from the plumbing on purpose: 'handleMessage' is
-- a pure function from (state, request) to (state, replies), so the whole
-- server can be exercised in the test suite without a socket or a subprocess.
-- 'runLsp' is only the thin IO loop that reads frames, calls 'handleMessage',
-- and writes frames back.
module Zkc.Lsp
  ( runLsp
    -- * Pure core (exposed for testing)
  , ServerState(..)
  , initialState
  , handleMessage
  , diagnosticToLsp
  , frame
  , utf8Length
  ) where

import Data.Bits (shiftL, shiftR, (.&.), (.|.))
import Data.Char (chr, ord)
import Data.List (isPrefixOf)
import qualified Data.Map.Strict as Map
import Data.Word (Word8)
import System.IO

import qualified Data.ByteString as BS

import Zkc.Diagnose (diagnoseSource, hoverAt)
import Zkc.Diagnostics
import Zkc.Json (Json(..), encode, parse)
import Zkc.Profile (LineCost(..), profileSource)

-- | Everything the server remembers between messages: the open documents by
-- URI, and the field the analysis runs over.
data ServerState = ServerState
  { stDocs :: Map.Map String String
  , stField :: String
  } deriving (Eq, Show)

initialState :: ServerState
initialState = ServerState Map.empty "bn254"

-- JSON navigation helpers ----------------------------------------------

objLookup :: String -> Json -> Maybe Json
objLookup k (JObj kvs) = lookup k kvs
objLookup _ _ = Nothing

asStr :: Json -> Maybe String
asStr (JStr s) = Just s
asStr _ = Nothing

asInt :: Json -> Maybe Int
asInt (JInt n) = Just (fromIntegral n)
asInt _ = Nothing

-- | Follow a path of object keys, e.g. @["textDocument","uri"]@.
jpath :: [String] -> Json -> Maybe Json
jpath [] j = Just j
jpath (k : ks) j = objLookup k j >>= jpath ks

jstr :: [String] -> Json -> Maybe String
jstr ks j = jpath ks j >>= asStr

jint :: [String] -> Json -> Maybe Int
jint ks j = jpath ks j >>= asInt

-- | Full-sync @didChange@ sends the whole document as the @text@ of a change
-- entry; take the last one.
changeText :: Json -> Maybe String
changeText params = case objLookup "contentChanges" params of
  Just (JArr changes) | not (null changes) ->
    objLookup "text" (last changes) >>= asStr
  _ -> Nothing

-- Message construction -------------------------------------------------

jsonrpc :: (String, Json)
jsonrpc = ("jsonrpc", JStr "2.0")

response :: Maybe Json -> Json -> Json
response mid result =
  JObj [jsonrpc, ("id", maybe JNull id mid), ("result", result)]

errorResponse :: Maybe Json -> Integer -> String -> Json
errorResponse mid code message =
  JObj [ jsonrpc, ("id", maybe JNull id mid)
       , ("error", JObj [("code", JInt code), ("message", JStr message)]) ]

notification :: String -> Json -> Json
notification method params =
  JObj [jsonrpc, ("method", JStr method), ("params", params)]

-- | The one capability set that matters: full-document sync (so we always have
-- the current text) and hover (the proof, surfaced on demand).
initializeResult :: Json
initializeResult = JObj
  [ ("capabilities", JObj
      [ ("textDocumentSync", JInt 1)      -- 1 = full
      , ("hoverProvider", JBool True)
      , ("inlayHintProvider", JBool True) ])
  , ("serverInfo", JObj [("name", JStr "zkc-lsp")]) ]

-- Diagnostics ----------------------------------------------------------

-- | Map one of our diagnostics to an LSP @Diagnostic@. LSP positions are
-- zero-based, ours are one-based; a missing line pins to the top of the file
-- and a missing column to the start of the line. Notes and help ride along in
-- the message so they show in the editor's hover-over-squiggle.
diagnosticToLsp :: Diagnostic -> Json
diagnosticToLsp d = JObj
  [ ("range", JObj
      [ ("start", pos line0 char0)
      , ("end", pos line0 (char0 + 1)) ])
  , ("severity", JInt 1)          -- 1 = Error
  , ("source", JStr "zkc")
  , ("message", JStr fullMessage)
  ]
  where
    line0 = maybe 0 (\l -> max 0 (l - 1)) (diagLine d)
    char0 = maybe 0 (\c -> max 0 (c - 1)) (diagCol d)
    pos l c = JObj [("line", JInt (fromIntegral l)), ("character", JInt (fromIntegral c))]
    fullMessage = unlines' (diagMessage d : diagNotes d ++ helpLine)
    helpLine = maybe [] (\h -> ["help: " ++ h]) (diagHelp d)
    unlines' = foldr1 (\a b -> a ++ "\n" ++ b)

-- | The @publishDiagnostics@ notification for a URI's current text.
publishFor :: ServerState -> String -> Json
publishFor st uri = notification "textDocument/publishDiagnostics" $ JObj
  [ ("uri", JStr uri)
  , ("diagnostics", JArr diags) ]
  where
    diags = case Map.lookup uri (stDocs st) of
      Just text -> map diagnosticToLsp (diagnoseSource (stField st) text)
      Nothing -> []

publishEmpty :: String -> Json
publishEmpty uri = notification "textDocument/publishDiagnostics" $ JObj
  [ ("uri", JStr uri), ("diagnostics", JArr []) ]

-- The pure protocol handler --------------------------------------------

-- | Handle one incoming message: return the updated state and the messages to
-- send back (a response for a request, notifications for document events, or
-- nothing). Pure, so the whole conversation is testable.
handleMessage :: ServerState -> Json -> (ServerState, [Json])
handleMessage st msg =
  case objLookup "method" msg >>= asStr of
    Just "initialize" -> (st, [response mid initializeResult])
    Just "initialized" -> (st, [])
    Just "textDocument/didOpen" ->
      case (jstr ["textDocument", "uri"] params, jstr ["textDocument", "text"] params) of
        (Just uri, Just text) ->
          let st' = st { stDocs = Map.insert uri text (stDocs st) }
          in (st', [publishFor st' uri])
        _ -> (st, [])
    Just "textDocument/didChange" ->
      case (jstr ["textDocument", "uri"] params, changeText params) of
        (Just uri, Just text) ->
          let st' = st { stDocs = Map.insert uri text (stDocs st) }
          in (st', [publishFor st' uri])
        _ -> (st, [])
    Just "textDocument/didClose" ->
      case jstr ["textDocument", "uri"] params of
        Just uri -> (st { stDocs = Map.delete uri (stDocs st) }, [publishEmpty uri])
        Nothing -> (st, [])
    Just "textDocument/hover" -> (st, [response mid (hoverResult st params)])
    Just "textDocument/inlayHint" -> (st, [response mid (inlayHints st params)])
    Just "shutdown" -> (st, [response mid JNull])
    Just "exit" -> (st, [])
    Just _ -> case mid of
      Just _ -> (st, [errorResponse mid (-32601) "method not found"])
      Nothing -> (st, [])
    Nothing -> (st, [])
  where
    mid = objLookup "id" msg
    params = maybe JNull id (objLookup "params" msg)

-- | Hover: surface the determinacy proof for the output under the cursor.
-- LSP positions are zero-based; the analysis speaks one-based lines.
hoverResult :: ServerState -> Json -> Json
hoverResult st params = case jstr ["textDocument", "uri"] params of
  Nothing -> JNull
  Just uri -> case Map.lookup uri (stDocs st) of
    Nothing -> JNull
    Just text ->
      let line = maybe 0 id (jint ["position", "line"] params) + 1
          col = maybe 0 id (jint ["position", "character"] params) + 1
      in case hoverAt (stField st) text line col of
           Nothing -> JNull
           Just markdown -> JObj
             [ ("contents", JObj
                 [ ("kind", JStr "markdown"), ("value", JStr markdown) ]) ]

-- | Inlay hints: each source line's cost, mirroring @zkc-profile@, placed at
-- the end of the line. The backend profiler's numbers are canonical; this
-- surfaces the same unfused accounting inline while editing.
inlayHints :: ServerState -> Json -> Json
inlayHints st params = case jstr ["textDocument", "uri"] params of
  Nothing -> JArr []
  Just uri -> case Map.lookup uri (stDocs st) of
    Nothing -> JArr []
    Just text -> JArr (map (hint text) (profileSource (stField st) text))
  where
    hint text (LineCost line r p) = JObj
      [ ("position", JObj
          [ ("line", JInt (fromIntegral (line - 1)))
          , ("character", JInt (fromIntegral (lineLength text line))) ])
      , ("label", JStr (" " ++ show r ++ " constraints, " ++ show p ++ " rows"))
      , ("paddingLeft", JBool True) ]

-- | Character length of a 1-based source line (0 if out of range).
lineLength :: String -> Int -> Int
lineLength text n =
  let ls = lines text
  in if n >= 1 && n <= length ls then length (ls !! (n - 1)) else 0

-- Framing (Content-Length over UTF-8) ----------------------------------

-- | Number of UTF-8 bytes a string occupies. LSP's @Content-Length@ counts
-- bytes, not characters, and our messages carry non-ASCII (the em dash in a
-- determinacy explanation), so this must be exact.
utf8Length :: String -> Int
utf8Length = sum . map width
  where
    width c
      | n < 0x80    = 1
      | n < 0x800   = 2
      | n < 0x10000 = 3
      | otherwise   = 4
      where n = ord c

utf8Encode :: String -> [Word8]
utf8Encode = concatMap enc
  where
    enc c
      | n < 0x80    = [fromIntegral n]
      | n < 0x800   = [ 0xC0 .|. fromIntegral (n `shiftR` 6)
                      , cont n 0 ]
      | n < 0x10000 = [ 0xE0 .|. fromIntegral (n `shiftR` 12)
                      , cont n 6, cont n 0 ]
      | otherwise   = [ 0xF0 .|. fromIntegral (n `shiftR` 18)
                      , cont n 12, cont n 6, cont n 0 ]
      where n = ord c
    cont n s = 0x80 .|. fromIntegral ((n `shiftR` s) .&. 0x3F)

-- | Decode a complete UTF-8 byte sequence. Malformed bytes decode to U+FFFD so
-- a bad frame never crashes the loop.
utf8Decode :: [Word8] -> String
utf8Decode = go
  where
    go [] = []
    go (b0 : rest)
      | b0 < 0x80 = chr (fromIntegral b0) : go rest
      | b0 >= 0xF0 = case rest of
          (b1 : b2 : b3 : r) -> assemble [b0 .&. 0x07, b1, b2, b3] : go r
          _ -> [replacement]
      | b0 >= 0xE0 = case rest of
          (b1 : b2 : r) -> assemble [b0 .&. 0x0F, b1, b2] : go r
          _ -> [replacement]
      | b0 >= 0xC0 = case rest of
          (b1 : r) -> assemble [b0 .&. 0x1F, b1] : go r
          _ -> [replacement]
      | otherwise = replacement : go rest
    assemble (lead : conts) =
      chr (foldl (\acc b -> shiftL acc 6 .|. fromIntegral (b .&. 0x3F))
                 (fromIntegral lead) conts)
    assemble [] = replacement
    replacement = chr 0xFFFD

-- | Wrap a JSON message in its @Content-Length@ frame (as a String; the IO
-- writer turns it into UTF-8 bytes).
frame :: Json -> String
frame json =
  let body = encode json
  in "Content-Length: " ++ show (utf8Length body) ++ "\r\n\r\n" ++ body

-- The IO loop ----------------------------------------------------------

-- | Run the server: read framed JSON-RPC on stdin, reply on stdout, until EOF
-- or @exit@.
runLsp :: IO ()
runLsp = do
  hSetBinaryMode stdin True
  hSetBinaryMode stdout True
  hSetBuffering stdout (BlockBuffering Nothing)
  loop initialState
  where
    loop st = do
      mbody <- readFrame
      case mbody of
        Nothing -> pure ()
        Just body -> case parse body of
          Left _ -> loop st                       -- ignore malformed frames
          Right msg -> do
            let (st', replies) = handleMessage st msg
            mapM_ writeMessage replies
            case objLookup "method" msg >>= asStr of
              Just "exit" -> pure ()
              _ -> loop st'

writeMessage :: Json -> IO ()
writeMessage json = do
  let header = "Content-Length: " ++ show (utf8Length body) ++ "\r\n\r\n"
      body = encode json
  BS.hPut stdout (BS.pack (map (fromIntegral . ord) header))
  BS.hPut stdout (BS.pack (utf8Encode body))
  hFlush stdout

-- | Read one framed message: parse headers for @Content-Length@, then read
-- exactly that many bytes and decode them. 'Nothing' on EOF.
readFrame :: IO (Maybe String)
readFrame = do
  mlen <- readHeaders Nothing
  case mlen of
    Nothing -> pure Nothing
    Just n -> do
      bytes <- BS.hGet stdin n
      if BS.length bytes < n
        then pure Nothing
        else pure (Just (utf8Decode (BS.unpack bytes)))

readHeaders :: Maybe Int -> IO (Maybe Int)
readHeaders acc = do
  mline <- readHeaderLine
  case mline of
    Nothing -> pure Nothing
    Just "" -> pure acc                            -- blank line terminates headers
    Just line
      | "Content-Length:" `isPrefixOf` line ->
          readHeaders (Just (read (trim (drop (length "Content-Length:") line))))
      | otherwise -> readHeaders acc               -- ignore Content-Type, etc.
  where
    trim = dropWhile (== ' ') . reverse . dropWhile (== ' ') . reverse

-- | Read a single header line (ASCII), consuming the terminating LF and
-- stripping a trailing CR.
readHeaderLine :: IO (Maybe String)
readHeaderLine = go []
  where
    go acc = do
      b <- BS.hGet stdin 1
      if BS.null b
        then pure (if null acc then Nothing else Just (stripCR (reverse acc)))
        else let c = chr (fromIntegral (BS.head b))
             in if c == '\n' then pure (Just (stripCR (reverse acc)))
                             else go (c : acc)
    stripCR s = if not (null s) && last s == '\r' then init s else s