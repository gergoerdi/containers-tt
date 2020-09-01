{-# OPTIONS --type-in-type #-}

open import Relation.Binary.PropositionalEquality
  renaming (trans to infixr 4 _◾_)
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Relation.Nullary
open import Data.Product
open import Function using (_∘_)
import Axiom.Extensionality.Propositional as Axiom

module _ where

postulate
  funExt  : ∀ {i j} → Axiom.Extensionality i j
  funExti : ∀ {i j} → Axiom.ExtensionalityImplicit i j

uip : ∀ {A : Set}{x y : A}(p q : x ≡ y) → p ≡ q
uip refl refl = refl

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
      mor : ∀ {A B : Ob} → Mor A B → pt B → pt A
      id : ∀ {A} {y : pt A} → mor id y ≡ y
      comp : ∀ {A B C} (f : Mor B C) (g : Mor A B) → ∀ y → mor (f ∙ g) y ≡ mor g (mor f y)
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
      nat : ∀ {A B} {f : Mor A B} → ∀ (γ : pt Γ B) → mor Δ f (fun γ) ≡ fun (mor Γ f γ)
  open Sub public

  record Ty (Γ : Con) : Set where
    field
      ty : ∀ {A} (γ : pt Γ A) → Set
      mor : ∀ {A B} (f : Mor A B) {γA : pt Γ A} {γB : pt Γ B} → mor Γ f γB ≡ γA  → ty γB → ty γA
      id : ∀ {A} {γ : pt Γ A} (t : ty γ) → mor C.id (id Γ) t ≡ t

      comp : ∀ {A B C} (f : Mor B C) (g : Mor A B) {γA : pt Γ A} {γB : pt Γ B} {γC : pt Γ C} →
        (eq-f : Con.mor Γ f γC ≡ γB) →
        (eq-g : Con.mor Γ g γB ≡ γA) →
        (t : ty γC) →
        mor (f ∙ g) (Con.comp Γ f g γC ◾ cong _ eq-f ◾ eq-g) t ≡ mor g eq-g (mor f eq-f t)
  open Ty public

  infix 6 _[_]T
  _[_]T : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
  _[_]T {Γ} {Δ} A σ = record
    { ty = λ γ → ty A (fun σ γ)
    ; mor = λ f {γA} {γB} eq → mor A f (nat σ {f = f} γB ◾ cong (fun σ) eq )
    -- ; id = λ t → cong (λ ξ → mor A C.id ξ t) {!uip !} ◾ id A t
    ; id = λ t → cong₂ (mor A C.id) (uip _ _) refl ◾ id A t
    ; comp = λ f g eq-f eq-g t → {!comp A f g!}
    }

  _▶_ : (Γ : Con) → Ty Γ → Con
  Γ ▶ t = record
    { pt = λ A → Σ (pt Γ A) (ty t)
    ; mor = λ {A} {B} ϕ (γ , e) → mor Γ ϕ γ , mor t {!!} {!!} e
    ; id = {!!}
    ; comp = {!!}
    }

  wk : ∀ {Γ A} → Sub (Γ ▶ A) Γ
  wk = record
    { fun = proj₁
    ; nat = λ _ → refl
    }

  record Tm (Γ : Con) (t : Ty Γ) : Set where
    field
      tm : ∀ {A} (γ : pt Γ A) → ty t γ
      nat : ∀ {A B} (f : Mor A B) {γA : Con.pt Γ A} {γB : Con.pt Γ B} →
        (e : mor Γ f γB ≡ γA) → mor t f e (tm γB) ≡ tm γA
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

  C0 : Container
  C0 = record { shape = ⊥ ; positions = ⊥-elim }

  fromC0 : ∀ C → Map C0 C
  fromC0 C = record
    { reshape = ⊥-elim
    ; reposition = λ {sh} _ → ⊥-elim sh
    }

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

  lift : Container → ∀ {Γ} → Ty Γ
  lift X = record
    { ty = λ {A} _ → Map A X
    ; mor = λ f eq ϕ → record { reshape = reshape ϕ ∘ reshape f ; reposition = reposition f ∘ reposition ϕ }
    ; id = λ _ → refl
    ; comp = {!!}
    }

  Bot : ∀ {Γ} → Ty Γ
  -- Bot = lift C0
  Bot = record
    { ty = λ _ → ⊥
    ; mor = λ ϕ eq bot → bot
    ; id = λ _ → refl
    ; comp = λ _ _ _ _ _ → refl
    }

  elimBot : ∀ {Γ} (A : Ty Γ) → Tm Γ Bot → Tm Γ A
  elimBot {Γ} A bot = record
    { tm = λ γ → ⊥-elim (tm bot γ)
    ; nat = {!!}
    }

  Π : ∀ {Γ}(A : Ty Γ) → Ty (Γ ▶ A) → Ty Γ
  Π A B = record
    { ty = λ γ →
         ∃ λ (f : (α : ty A γ) → ty B (γ , α)) →
             (∀ {α : ty A γ} → {!!} → {!!} )
    ; mor = λ ϕ eq (f , q) → {!!} , {!!}
    ; id = {!!}
    ; comp = {!!}
    }

  lam : ∀ {Γ} (A : Ty Γ) {B : Ty (Γ ▶ A)} → Tm (Γ ▶ A) B → Tm Γ (Π A B)
  lam t e = record
    { tm = λ γ → (λ α → tm e (γ , α)) , {!!}
    ; nat = {!!}
    }

  A : Ty []
  A = lift C2

  B : Ty ([] ▶ A)
  B = lift C1

  liftFun : ∀ {X Y} → Map X Y → Tm ([] ▶ lift X) (lift Y)
  liftFun f = record
    { tm = λ {A} (_ , ϕ) → record { reshape = reshape f ∘ reshape ϕ ; reposition = reposition ϕ ∘ reposition f }
    ; nat = λ _ eq → {!!}
    }
