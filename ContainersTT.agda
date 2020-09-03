{-# OPTIONS --type-in-type #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Function using (_∘_; id)

open import TT
open import Containers

module _ where

Ty : (Γ : Container) → Set
Ty = Refinement

Tm : (Γ : Container) (A : Ty Γ) → Set
Tm = Extension

ttSyntax : Syntax
ttSyntax = record
  { Con = Container
  ; Sub = Map
  ; Ty = Ty
  ; Tm = Tm

  ; [] = con ⊤ λ _ → ⊥
  ; _▶_ = refine

  ; _[_]T = {!!}
  ; _[_]t = {!!}
  }
