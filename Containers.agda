{-# OPTIONS --type-in-type #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product
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

mapR : ∀ {Γ Δ} → Map Γ Δ → Refinement Δ → Refinement Γ
mapR {Γ} {Δ} f R = refinement (ornament R ∘ reshape f) (position R)

data Source (Γ : Container) (sh : shape Γ) (R : Refinement Γ) (o : ornament R sh) : Set where
  old : position Γ sh → Source Γ sh R o
  new : position R o → Source Γ sh R o

map-new : ∀ {Γ R sh o} → (position R o -> position Γ sh) → Source Γ sh R o → position Γ sh
map-new f (old p) = p
map-new f (new q) = f q

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

mapE : ∀ {Γ Δ R} (f : Map Γ Δ) → (e : Extension Δ R) → Extension Γ (mapR f R)
mapE f e = extension (decorate e ∘ reshape f) (reposition f ∘ reposition e)

coarse : ∀ {Γ Δ R} → Map Γ (refine Δ R) → Map Γ Δ
coarse f = cmap (proj₁ ∘ reshape f) (reposition f ∘ old)

-- TODO: rename
π₂ : ∀ {Γ Δ R}(f : Map Γ (refine Δ R)) → Extension Γ (mapR (coarse f) R)
π₂ f = extension (proj₂ ∘ reshape f) (reposition f ∘ new)
