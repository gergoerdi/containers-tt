{-# OPTIONS --type-in-type #-}

open import Relation.Binary.PropositionalEquality
open import Function using (_∘_)

module CT where

record Category : Set where
  infixr 5 _∙_
  field
    Ob : Set
    Mor : Ob → Ob → Set
    _∙_ : ∀ {A B C} (f : Mor B C) (g : Mor A B) → Mor A C
    id : ∀ {A} → Mor A A
    ass : ∀ {A B C D} (f : Mor C D) (g : Mor B C) (h : Mor A B) → f ∙ (g ∙ h) ≡ (f ∙ g) ∙ h

Agda : Category
Agda = record
  { Ob = Set
  ; Mor = λ A B → A → B
  ; _∙_ = λ f g → f ∘ g
  ; id = λ x → x
  ; ass = λ f g h → refl
  }
