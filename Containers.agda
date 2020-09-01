{-# OPTIONS --type-in-type #-}

open import Relation.Binary.PropositionalEquality
--   renaming (trans to infixr 4 _◾_; subst to tr; cong to ap; sym to infix 6 _⁻¹)
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Relation.Nullary
open import Data.Product
-- open import Data.Sum
open import Function using (_∘_)
-- open import Function using (_∋_)
-- open import Level
import Axiom.Extensionality.Propositional as Axiom

module _ where

postulate
  funExt  : ∀ {i j} → Axiom.Extensionality i j
  funExti : ∀ {i j} → Axiom.ExtensionalityImplicit i j

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

open CT

module CwF (C : Category) where
  module C = Category C
  open C

  record Con : Set where
    field
      pt : Ob → Set
      mor : ∀ {A B : Ob} → Mor A B → pt A → pt B
      id : ∀ {A} {y : pt A} → mor id y ≡ y
      comp : ∀ {A B C} (f : Mor B C) (g : Mor A B) → ∀ y → mor (f ∙ g) y ≡ mor f (mor g y)
  open Con public

  [] : Con
  [] = record
    { pt = λ _ → ⊤
    ; mor = λ _ _ → _
    ; id = refl
    ; comp = λ f g _ → refl
    }

  record Sub (Γ Δ : Con) : Set where
    field
      fun : ∀ {A} → pt Γ A → pt Δ A
      nat : ∀ {A B} {f : Mor A B} → ∀ (γ : pt Γ A) → mor Δ f (fun γ) ≡ fun (mor Γ f γ)

  record Ty (Γ : Con) : Set where
    field
      pt : ∀ {A} (γ : pt Γ A) → Set
      mor : ∀ {A B} (f : Mor A B) {γA : Con.pt Γ A} {γB : Con.pt Γ B} → Con.mor Γ f γA ≡ γB  → pt γB → pt γA
      id : ∀ {A} {γ : Con.pt Γ A} (t : pt γ) → mor C.id (id Γ) t ≡ t

      comp : ∀ {A B C} (f : Mor B C) (g : Mor A B) {γA : Con.pt Γ A} {γB : Con.pt Γ B} {γC : Con.pt Γ C} →
        (eq-f : Con.mor Γ f γB ≡ γC) →
        (eq-g : Con.mor Γ g γA ≡ γB) →
        (t : pt γA) →
        {!mor (f ∙ g) (trans {!!} eq-f) t ≡ mor f eq-f (mor g eq-g t)!}
      --     -- morph-comp : ∀ {x y z} (f : Hom x y) (g : Hom y z) {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} →
      --     --        (eq-zy : Γ ⟪ g ⟫ γz ≡ γy) (eq-yx : Γ ⟪ f ⟫ γy ≡ γx) (t : type z γz) →
      --     --        morph (g ∙ f) (strong-rel-comp Γ eq-zy eq-yx) t ≡ morph f eq-yx (morph g eq-zy t)
  open Ty public

  _▶_ : (Γ : Con) → Ty Γ → Con
  Γ ▶ t = record
    { pt = λ A → Σ (pt Γ A) (pt t)
    ; mor = {!!}
    ; id = {!!}
    ; comp = {!!}
    }

  record Tm (Γ : Con) (t : Ty Γ) : Set where
    field
      pt : ∀ {A} (γ : pt Γ A) → pt t γ
      nat : ∀ {A B} (f : Mor A B) {γA : Con.pt Γ A} {γB : Con.pt Γ B} →
        (e : mor Γ f γA ≡ γB) → mor t f e (pt γB) ≡ pt γA
  open Tm public

module Containers where
  record Container : Set where
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
    ; id = record { reshape = λ sh → sh ; reposition = λ pos → pos }
    ; ass = λ f g h → refl
    }

module Containers-CwF where
  open Containers
  open Category Containers.category

  C1 : Container
  C1 = record { shape = ⊤ ; positions = λ _ → ⊤ }

  C2 : Container
  C2 = record { shape = ⊤; positions = λ _ → Bool }

  f : Mor C2 C1
  f = record
    { reshape = λ _ → _
    ; reposition = λ _ → true
    }

  g : Mor C2 C1
  g = record
    { reshape = λ _ → _
    ; reposition = λ _ → false
    }

  fT≢fF : ¬ (f ≡ g)
  fT≢fF eq = true≢false (lemma eq)
    where
      lemma : f ≡ g → true ≡ false
      lemma = cong (λ x → reposition x tt)

      true≢false : ¬ (true ≡ false)
      true≢false ()

  open CwF Containers.category

  lift : ∀ {Γ} → (X : Container) → Ty Γ
  lift X = record
    { pt = λ {A} _ → Map A X
    ; mor = λ f eq ϕ → record { reshape = reshape ϕ ∘ reshape f ; reposition = reposition f ∘ reposition ϕ }
    ; id = λ _ → refl
    }

  A : Ty []
  A = lift C2

  B : Ty ([] ▶ A)
  B = lift C1

  liftFun : ∀ {X Y} → Map X Y → Tm ([] ▶ lift X) (lift Y)
  liftFun f = record
    { pt = λ {A} (_ , ϕ) → record { reshape = reshape f ∘ reshape ϕ ; reposition = reposition ϕ ∘ reposition f }
    ; nat = λ _ _ → {!!}
    }

  -- f₀ : Tm ([] ▶ A) B
  -- f₀ = record
  --   { pt = λ (_ , ϕ) → record
  --     { reshape = λ _ → reshape ϕ tt
  --     ; reposition = {!!}
  --     }
  --   ; nat = {!!}
  --   }
