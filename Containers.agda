{-# OPTIONS --type-in-type #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Data.Maybe
open import Function using (_∘_; id)

open import CT

module _ where

record Container : Set where
  constructor con
  field
    shape : Set
    position : shape → Set
open Container public

record Map (C D : Container) : Set where
  constructor cmap
  field
    reshape : shape C → shape D
    reposition : ∀ {sh : shape C} → (p : position D (reshape sh)) → position C sh
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
    position : {sh : shape Γ} (o : ornament sh) → Set
open Refinement public

data Source (Γ : Container) (sh : shape Γ) (R : Refinement Γ) (o : ornament R sh) : Set where
  old : position Γ sh → Source Γ sh R o
  new : position R o → Source Γ sh R o

map-new : ∀ {Γ R sh o} → (position R o -> position Γ sh) → Source Γ sh R o → position Γ sh
map-new f (old p) = p
map-new f (new q) = f q

from-new : ∀ {Γ R sh o} → Source Γ sh R o → Maybe (position R o)
from-new (old _) = nothing
from-new (new p) = just p

refine : (Γ : Container) → Refinement Γ → Container
refine Γ R = con (Σ (shape Γ) (ornament R)) λ (sh , o) → Source Γ sh R o

record Extension (Γ : Container) (P : Refinement Γ) : Set where
  constructor extension
  field
    decorate : (sh : shape Γ) → ornament P sh
    reposition : {sh : shape Γ} → position P {sh} (decorate sh) → position Γ sh
open Extension public

extend : (Γ : Container) {R : Refinement Γ} → (e : Extension Γ R) → Map Γ (refine Γ R)
extend Γ e = record
  { reshape = λ sh → sh , decorate e sh
  ; reposition = map-new (reposition e)
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
