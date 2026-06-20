-- This module serves as the root of the `LeanMenhir` library.
-- A verified LR(1) parser interpreter + validator, ported from `coq-menhirlib`,
-- plus an (untrusted) native LR(1) table generator certified by the validator.
import LeanMenhir.Alphabet
import LeanMenhir.Grammar
import LeanMenhir.Automaton
import LeanMenhir.Validator.Classes
import LeanMenhir.Validator.Safe
import LeanMenhir.Interpreter
import LeanMenhir.Interpreter.Correct
import LeanMenhir.Main
import LeanMenhir.Generator.FinAlphabet
import LeanMenhir.Generator.Tables
import LeanMenhir.Generator.LR1
import LeanMenhir.Examples.Arith
import LeanMenhir.Examples.MiniCalc
