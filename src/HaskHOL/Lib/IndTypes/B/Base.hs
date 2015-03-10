module HaskHOL.Lib.IndTypes.B.Base where

import HaskHOL.Core

import HaskHOL.Lib.Recursion
import HaskHOL.Lib.Nums

import HaskHOL.Lib.IndTypes.B.Pre
import HaskHOL.Lib.IndTypes.A

indDefSum' :: IndTypesACtxt thry => HOL Theory thry (HOLThm, HOLThm)
indDefSum' = defineTypeRaw =<< 
    parseInductiveTypeSpecification "sum = INL A | INR B"

defOUTL' :: NumsCtxt thry => HOLThm -> HOL Theory thry HOLThm
defOUTL' th = newRecursiveDefinition "OUTL" th
    [str| OUTL (INL x :A+B) = x |]

defOUTR' :: NumsCtxt thry => HOLThm -> HOL Theory thry HOLThm
defOUTR' th = newRecursiveDefinition "OUTR" th
    [str| OUTR (INR y :A+B) = y |]
