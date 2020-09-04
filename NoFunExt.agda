{-# OPTIONS --type-in-type #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Relation.Nullary
open import Function using (_∘_; id)

open import Containers

module _ where

C0 : Container
C0 = con ⊥ λ ()

fromC0 : ∀ C → Map C0 C
fromC0 C = record
  { reshape = ⊥-elim
  ; reposition = λ {sh} _ → ⊥-elim sh
  }

C∞ : Container
C∞ = con ⊤ λ _ → ⊥

toC∞ : ∀ C → Map C C∞
toC∞ C = record
  { reshape = λ _ → tt
  ; reposition = λ ()
  }

C1 : Container
C1 = con ⊤ λ _ → ⊤

C2 : Container
C2 = con ⊤ λ _ → Bool

f g : Map C2 C1
f = record { reshape = λ _ → _ ; reposition = λ _ → true }
g = record { reshape = λ _ → _ ; reposition = λ _ → false }

f≢g : ¬ (f ≡ g)
f≢g eq = true≢false (lemma eq)
  where
    lemma : f ≡ g → true ≡ false
    lemma = cong (λ x → reposition x tt)

    true≢false : ¬ (true ≡ false)
    true≢false ()
