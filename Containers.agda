{-# OPTIONS --type-in-type #-}

open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Product
open import Relation.Nullary
open import Function using (_∘_)

open import CT

module _ where

record Container : Set where
  constructor con
  field
    shape : Set
    positions : shape → Set
open Container public

record Map (C D : Container) : Set where
  field
    reshape : shape C → shape D
    reposition : ∀ {sh : shape C} → (p : positions D (reshape sh)) → positions C sh
open Map public

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

category : Category
category = record
  { Ob = Container
  ; Mor = Map
  ; _∙_ = λ f g → record { reshape = reshape f ∘ reshape g ; reposition = reposition g ∘ reposition f }
  ; id = record { reshape = λ sh → sh ; reposition = λ pos → pos }
  ; ass = λ f g h → refl
  }

open import TT

ttSyntax : Syntax
ttSyntax = record
  { Con = Container
  ; Sub = Map
  ; Ty = λ Γ →
       ∃ λ (P : shape Γ → Set) →
           ∀ {sh : shape Γ} (α : P sh) → Set
  ; Tm = λ Γ (P , R) →
       ∃ λ (P : (sh : shape Γ) → P sh) →
           ∀ {sh : shape Γ} → R {sh} (P sh) → positions Γ sh

  ; [] = con ⊤ λ _ → ⊥
  ; _▶_ = {!!}

  ; _[_]T = {!!}
  ; _[_]t = {!!}
  }
