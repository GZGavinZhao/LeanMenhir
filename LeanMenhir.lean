-- This module serves as the root of the `LeanMenhir` library.
-- A verified LR(1) parser interpreter + validator, ported from `coq-menhirlib`,
-- plus an (untrusted) native LR(1) table generator certified by the validator.
import LeanMenhir.Spec.Alphabet
import LeanMenhir.Spec.Grammar
import LeanMenhir.Spec.Language
import LeanMenhir.Machine.Automaton
import LeanMenhir.Correctness.Classes
import LeanMenhir.Correctness.Safe
import LeanMenhir.Correctness.Complete
import LeanMenhir.Machine.Interpreter
import LeanMenhir.Correctness.Sound
import LeanMenhir.Correctness.CompleteProof
import LeanMenhir.Correctness.Congr
import LeanMenhir.Correctness.Anchored
import LeanMenhir.Main
import LeanMenhir.Runtime
import LeanMenhir.Guarantees
import LeanMenhir.Generator.FinAlphabet
import LeanMenhir.Generator.Tables
import LeanMenhir.Generator.Grammar0
import LeanMenhir.Generator.Derives0
import LeanMenhir.Generator.LR1
import LeanMenhir.Generator.BuildTables
import LeanMenhir.Examples.Arith
import LeanMenhir.Examples.MiniCalc
import LeanMenhir.Examples.StmCalc
import LeanMenhir.Examples.CalcTemplate
import LeanMenhir.Examples.ScaleTest
