-- | From source text to diagnostics, as a library.
--
-- Phase 6's tooling (the language server, and any \"just check this\" caller)
-- must produce exactly the diagnostics the CLI does — the same determinacy
-- proof turned into the same message. Rather than let that logic live in the
-- @zkc@ executable where only the CLI can reach it, it lives here, and both
-- the CLI and the server import it. That is the phase-6 discipline: tooling
-- reuses the compiler as a library, it does not re-derive it.
--
-- 'diagnoseSource' runs the pipeline over the decidable determinacy core
-- only: parse, elaborate, then the monomorphic-in-IO analysis. No solver is
-- shelled out and nothing touches the filesystem, so an editor can call it on
-- every keystroke. The solver-escalation verdicts (refutation, residual) keep
-- their diagnostic constructors here too, for the CLI's IO path to use.
module Zkc.Diagnose
  ( diagnoseSource
  , hoverAt
  , determinacyDiagnostic
  , refutationDiagnostic
  , residualDiagnostic
  , nameInBody
  ) where

import Data.List (intercalate)

import Zkc.Analysis.Determinacy
import Zkc.Analysis.Smt (Counterexample(..), Residual(..), renderCounterexample)
import Zkc.Core.Elaborate (elaborate, Elaborated(..))
import Zkc.Core.Ir
import Zkc.Diagnostics
import Zkc.Field (fieldModulus, knownFields)
import Zkc.Syntax.Ast (Visibility(..))
import Zkc.Syntax.Parser (parseProgram)

-- | The whole front end as a pure function: source and field name in, the
-- diagnostics an author should see out. Empty means the circuit parsed,
-- elaborated and was proved determinate by the decidable core.
diagnoseSource :: String -> String -> [Diagnostic]
diagnoseSource field source =
  case parseProgram source of
    Left d -> [d]
    Right program -> case elaborate field program of
      Left d -> [d]
      Right e -> case fieldModulus field of
        Nothing -> [unknownField field]
        Just modulus ->
          case checkProgram modulus (elabGadgetBodies e) (elabCircuitBody e) of
            Left problem -> [determinacyDiagnostic problem]
            Right _ -> []

-- | The same \"unknown field\" message the CLI's 'prepare' step emits.
unknownField :: String -> Diagnostic
unknownField field =
  withHelp ("known fields: " ++ unwords (map fst knownFields))
  $ diag ("unknown field '" ++ field ++ "'; the determinacy analysis needs its "
          ++ "modulus to decide whether a coefficient is nonzero")

-- Hover: the determinacy proof, surfaced on demand ---------------------
--
-- The @--explain@ flag prints the case splits a determinacy proof used; a
-- hover is the same information, delivered where the cursor is. Given a
-- one-based line, we look for an output /declared/ on that line and report
-- what the analysis concluded about it: proved determined (with the cases, if
-- any), or — for the output the proof got stuck on — why not.

-- | Markdown hover text for the position, or 'Nothing' when there is no output
-- to talk about there.
hoverAt :: String -> String -> Int -> Int -> Maybe String
hoverAt field source line _col =
  case parseProgram source >>= elaborate field of
    Left _ -> Nothing
    Right e -> case fieldModulus field of
      Nothing -> Nothing
      Just modulus ->
        let ir = elabIr e
            here = [ i | i <- irInputs ir, iiVisibility i == Output, iiLine i == line ]
        in case here of
             [] -> Nothing
             (out : _) -> Just (renderHover ir modulus (iiName out))

renderHover :: Ir -> Integer -> String -> String
renderHover ir modulus name = case checkDeterminacy modulus ir of
  Right report ->
    "**output `" ++ name ++ "`** — proved determined by the inputs.\n\n"
    ++ "Every witness that satisfies the constraints agrees on `" ++ name ++ "`."
    ++ casesSection ir report
  Left failure ->
    let failName = nameInIr ir (failTarget failure)
    in if failName == name
         then "**output `" ++ name ++ "`** — not determined by the inputs.\n\n"
              ++ failureExplanation ir failure
         else "**output `" ++ name ++ "`** — determinacy not established; the "
              ++ "analysis stopped at `" ++ failName ++ "`."

-- | The case splits the proof relied on, when it needed any.
casesSection :: Ir -> Report -> String
casesSection ir report = case filter (not . null) (repAssumptions report) of
  [] -> ""
  splits -> "\n\nProof by cases:\n"
            ++ concat [ "- " ++ intercalate ", " (map (renderAssump ir) c) ++ "\n" | c <- splits ]

failureExplanation :: Ir -> Failure -> String
failureExplanation ir failure = case failAssumptions failure of
  [] -> "The constraints admit more than one value for the same inputs, so the "
        ++ "prover chooses which one to prove."
  assumptions ->
    "Under " ++ intercalate " and " (map (renderAssump ir) assumptions)
    ++ ", the constraints admit more than one value — the prover chooses which."

nameInIr :: Ir -> WireId -> String
nameInIr ir wire =
  case [ iiName i | i <- irInputs ir, iiWire i == wire ] of
    (n : _) -> n
    [] -> case [ hiName info | (w, info) <- adviceWires ir, w == wire ] of
      (n : _) -> n
      [] -> "wire" ++ show wire

renderAssump :: Ir -> Assumption -> String
renderAssump ir a = case a of
  AssumeZero w -> nameInIr ir w ++ " == 0"
  AssumeNonZero w -> nameInIr ir w ++ " != 0"

nameInBody :: Body -> WireId -> String
nameInBody body wire =
  case [ iiName i | i <- bodyAtoms body, iiWire i == wire ] of
    (name : _) -> name
    [] -> case [ hiName info | Node w (OHint info _) <- bodyNodes body, w == wire ] of
      (name : _) -> name
      [] -> "wire" ++ show wire

renderAssumptionIn :: Body -> Assumption -> String
renderAssumptionIn body a = case a of
  AssumeZero w -> nameInBody body w ++ " == 0"
  AssumeNonZero w -> nameInBody body w ++ " != 0"

-- | Turn a failed determinacy proof into an error a circuit author can act on.
determinacyDiagnostic :: ProgramFailure -> Diagnostic
determinacyDiagnostic problem = case failNote failure of
  Just note -> withNotes [note] (diag ("the determinacy analysis could not finish" ++ context))
  Nothing ->
    withHelp ("add a constraint that forces '" ++ target
              ++ "' in this case, then recompile")
    $ withNotes (assumptionNote ++ adviceNote ++ [conclusion])
    $ pinned ("output '" ++ target ++ "' is not determined by the inputs" ++ context)
  where
    failure = pfFailure problem
    body = pfBody problem
    context
      | pfIsGadget problem = " of gadget '" ++ pfScope problem ++ "'"
      | otherwise = ""
    target = nameInBody body (failTarget failure)
    line = case [ iiLine i | i <- bodyAtoms body, iiWire i == failTarget failure, iiLine i > 0 ] of
      (l : _) -> l
      [] -> 1
    -- The declaring atom's column, when the frontend recorded one, so the
    -- caret lands on the offending output declaration (J.2).
    col = case [ iiCol i | i <- bodyAtoms body, iiWire i == failTarget failure, iiCol i > 0 ] of
      (c : _) -> Just c
      [] -> Nothing
    pinned = maybe (diagAt line) (diagAtCol line) col

    assumptionNote = case failAssumptions failure of
      [] -> ["the constraints admit more than one value of '" ++ target
             ++ "' for the same inputs"]
      assumptions ->
        [ "under the assumption "
          ++ intercalate " and " (map (renderAssumptionIn body) assumptions)
          ++ ", the constraints admit more than one value of '" ++ target ++ "'" ]

    adviceNote = case failFreeAdvice failure of
      [] -> []
      wires ->
        [ "the prover also chooses the advice "
          ++ (if length wires == 1 then "value " else "values ")
          ++ unwords [ "'" ++ nameInBody body w ++ "'" | w <- wires ] ++ " freely" ]

    conclusion =
      "so two witnesses can agree on every input and still disagree on '"
      ++ target ++ "' — the prover picks which one to prove"

-- | A refutation: not \"I could not prove this\" but \"here is the attack\".
refutationDiagnostic :: Integer -> Counterexample -> Diagnostic
refutationDiagnostic modulus cex =
  withHelp "add a constraint that rules out one of these two witnesses"
  $ withNotes (renderCounterexample modulus cex)
  $ diagAt (cxLine cex) ("'" ++ cxScope cex ++ "' is under-constrained — "
          ++ "the solver constructed a forgery")

-- | Honest incompleteness: neither proved nor refuted.
residualDiagnostic :: Residual -> Diagnostic
residualDiagnostic residual =
  withHelp helpText
  $ withNotes
      [ "this is not a claim that the circuit is wrong: the analysis ran out of"
      , "room before it could decide either way"
      ]
  $ diag ("could not decide whether '" ++ rsScope residual
          ++ "' is determined: " ++ rsReason residual)
  where
    helpText = case rsQueryPath residual of
      Just path -> "the query was written to " ++ path ++ "; try a longer \
                   \--smt-timeout, or a solver with finite-field support"
      Nothing -> "try a longer --smt-timeout, --dump-smt to inspect the query, \
                 \or a solver with finite-field support"