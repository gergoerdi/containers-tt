{-# OPTIONS --type-in-type #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Function using (_∘_; id)

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

category : Category
category = record
  { Ob = Container
  ; Mor = Map
  ; _∙_ = λ f g → record { reshape = reshape f ∘ reshape g ; reposition = reposition g ∘ reposition f }
  ; id = record { reshape = id ; reposition = id }
  ; ass = λ f g h → refl
  }

record Refinement (Γ : Container) : Set where
  constructor refinement
  field
    ornament : shape Γ → Set
    positions : {sh : shape Γ} (o : ornament sh) → Set
open Refinement

refine : (Γ : Container) → Refinement Γ → Container
refine Γ P = con (Σ (shape Γ) (ornament P)) λ (sh , o) → positions Γ sh ⊎ positions P o

record Extension (Γ : Container) (P : Refinement Γ) : Set where
  constructor extension
  field
    decorate : (sh : shape Γ) → ornament P sh
    reposition : {sh : shape Γ} → positions P {sh} (decorate sh) → positions Γ sh
open Extension

extend : (Γ : Container) {P : Refinement Γ} → (t : Extension Γ P) → Map Γ (refine Γ P)
extend Γ t = record
  { reshape = λ sh → sh , decorate t sh
  ; reposition = fromInj₁ (reposition t)
  }

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
