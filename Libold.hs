{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module Lib
    ( Symbol
    ) where

-- Basic Symbol declarations

newtype Symbol = Symbol String
newtype TypeIdentifier = TypeIdentifier Integer

{-
-- Expression
newtype Variable = Variable Symbol -- TODO: Maybe variables should be indexed by integers
data Expression where
  LambdaExpression :: Variable -> Expression -> Expression 
  Application :: Expression -> Expression -> Expression
  VariableExpression :: Variable -> Expression
  TypeExpression :: InhabitableType -> Expression

data InhabitableType = Type Type | Kind Kind | TypeOfKind

-- Context Definition
data Declaration = Declaration Symbol Type
newtype Context = Context [Declaration]

{- Not using anymore, was previously used to show 'A is a sort' for some A
data Sort = SortKind Kind | SortTypeOfKind
-}

-- Type Definition
data Type = Type TypeIdentifier | TypeArrow Type Type

-- Kind Definition
data Kind = KindType Type | KindArrow Kind Kind

-- The Type of a Kind
data TypeOfKind

-- Product Type
data ProductType

type (:::) = Judgement

type (:-) = Entails

data Entails a b where
  -- (sort)
  Sort :: Entails a KindIsASort
  -- 


-- Valid Judgements
data Judgement a b where
  -- Definition of a Sort
  KindIsASort :: Judgement Kind Sort
  TypeOfKindsIsASort :: Judgement TypeOfKind Sort

  -- (sort)
  -- The sort rule states, we know that a Kind has the type of `TypeOfKind`
  SortRule :: Judgement Kind TpeOfKind

  -- (var)
  {--
   - If we know A : B, and B is a sort (i.e. B is a kind or the type of kinds
   - Then we also know x : A --> x : A
  --}
  Var :: Judgement A B -> Judgement B Sort -> Judgement (LambdaExpression (Variable "x") (VariableExpression (Variable "x"))) (TypeArrow A A)
  -- (weak)
  Weak :: Judgement A B -> Judgement C D -> Judgement D Sort -> Judgement (LambdaExpression (Variable "x") (A)) (TypeArrow C B)
  -- (form)
  -- Form :: Judgement A Kind -> Judgement x ->
-}
