{-# LANGUAGE BangPatterns #-}

import Lib

-- The following file should run without errors

main :: IO ()
main = do
    let context = emptyContext
    let !proof = productTypeIsASort context

    putStrLn "Tests completed successfully"

assertEqual :: Eq a => a -> a -> Bool
assertEqual x y = (x == y) || error "Assertion failed"

{- 
 -
 - We should be able to show that` 
 - A --> * : TypeOfKind is deducible from A : *  
 -
 -}
productTypeIsASort :: Context -> Entailment
productTypeIsASort ctx = proofProductTypeIsASort
    where
        !kindIsSort = sort ctx []
        !assumptionThatAIsKind = enhance ctx (TypeExpression (Kind KindType))
        !aIsKind = var ctx [kindIsSort]
        !kindIsSort' = weak ctx [kindIsSort, aIsKind]
        !assumptionThatXHasTypeA = enhance ctx (materialise assumptionThatAIsKind)
        !kindIsSort'' = weak  ctx [kindIsSort', popEntailment assumptionThatXHasTypeA]
        !proofProductTypeIsASort = form ctx [aIsKind, kindIsSort'']
