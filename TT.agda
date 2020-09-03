{-# OPTIONS --type-in-type #-}

open import Relation.Binary.PropositionalEquality
open import Function using (_∘_)

module _ where

record Syntax : Set where
  field
    Con : Set
    Sub : Con → Con → Set
    Ty : (Γ : Con) → Set
    Tm : (Γ : Con) (A : Ty Γ) → Set

    [] : Con
    _▶_ : (Γ : Con) → Ty Γ → Con

    _[_]T : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
    _[_]t : ∀ {Γ Δ A} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
