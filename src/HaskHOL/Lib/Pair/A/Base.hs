{-# LANGUAGE ConstraintKinds, QuasiQuotes #-}
module HaskHOL.Lib.Pair.A.Base where

import HaskHOL.Core
import HaskHOL.Deductive

defLET' :: BoolCtxt thry => HOL Theory thry HOLThm
defLET' = newDefinition "LET"
    [str| LET (f:A->B) x = f x |]

defLET_END' :: BoolCtxt thry => HOL Theory thry HOLThm
defLET_END' = newDefinition "LET_END"
    [str| LET_END (t:A) = t |]

defGABS' :: BoolCtxt thry => HOL Theory thry HOLThm
defGABS' = newDefinition "GABS"
    [str| GABS (P:A->bool) = (@) P |]

defGEQ' :: BoolCtxt thry => HOL Theory thry HOLThm
defGEQ' = newDefinition "GEQ"
    [str| GEQ a b = (a:A = b) |]

def_SEQPATTERN' :: BoolCtxt thry => HOL Theory thry HOLThm
def_SEQPATTERN' = newDefinition "_SEQPATTERN"
    [str| _SEQPATTERN = \ r s x. if ? y. r x y then r x else s x |]

def_UNGUARDED_PATTERN' :: BoolCtxt thry => HOL Theory thry HOLThm
def_UNGUARDED_PATTERN' = newDefinition "_UNGUARDED_PATTERN"
    [str| _UNGUARDED_PATTERN = \ p r. p /\ r |]

def_GUARDED_PATTERN' :: BoolCtxt thry => HOL Theory thry HOLThm
def_GUARDED_PATTERN' = newDefinition "_GUARDED_PATTERN"
    [str| _GUARDED_PATTERN = \ p g r. p /\ g /\ r |]

def_MATCH' :: BoolCtxt thry => HOL Theory thry HOLThm
def_MATCH' = newDefinition "_MATCH"
    [str| _MATCH =  \ e r. if (?!) (r e) then (@) (r e) else @ z. F |]

def_FUNCTION' :: BoolCtxt thry => HOL Theory thry HOLThm
def_FUNCTION' = newDefinition "_FUNCTION"
    [str| _FUNCTION = \ r x. if (?!) (r x) then (@) (r x) else @ z. F |]

defMK_PAIR' :: BoolCtxt thry => HOL Theory thry HOLThm
defMK_PAIR' = newDefinition "mk_pair"
    [str| mk_pair (x:A) (y:B) = \ a b. (a = x) /\ (b = y) |]


