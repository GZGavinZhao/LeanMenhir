-- This module serves as the root of the `LeanMenhir` library.
-- A verified LR(1) parser interpreter + validator, ported from `coq-menhirlib`,
-- plus an (untrusted) native LR(1) table generator certified by the validator.
import LeanMenhir.Alphabet
import LeanMenhir.Grammar
import LeanMenhir.Language
import LeanMenhir.Automaton
import LeanMenhir.Validator.Classes
import LeanMenhir.Validator.Safe
import LeanMenhir.Validator.Complete
import LeanMenhir.Interpreter
import LeanMenhir.Interpreter.Correct
import LeanMenhir.Interpreter.Complete
import LeanMenhir.Interpreter.Congr
import LeanMenhir.Anchored
import LeanMenhir.Main
import LeanMenhir.Runtime
import LeanMenhir.Guarantees
import LeanMenhir.Generator.FinAlphabet
import LeanMenhir.Generator.Tables
import LeanMenhir.Generator.LR1
import LeanMenhir.Generator.BuildTables
import LeanMenhir.Generator.GrammarCheck
import LeanMenhir.Examples.Arith
import LeanMenhir.Examples.MiniCalc
import LeanMenhir.Examples.StmCalc
import LeanMenhir.Examples.CalcTemplate
import LeanMenhir.Examples.ScaleTest
