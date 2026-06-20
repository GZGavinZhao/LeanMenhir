-- This module serves as the root of the `LeanMenhir` library.
-- A verified LR(1) parser interpreter + validator, ported from `coq-menhirlib`.
import LeanMenhir.Alphabet
import LeanMenhir.Grammar
import LeanMenhir.Automaton
import LeanMenhir.Validator.Classes
import LeanMenhir.Validator.Safe
import LeanMenhir.Interpreter
import LeanMenhir.Interpreter.Correct
import LeanMenhir.Main
