-- https://github.com/JorisCeulemans/shallow-presheaf-embedding

{-# OPTIONS --type-in-type #-}

open import Relation.Binary.PropositionalEquality
  renaming (trans to infixr 4 _◾_)
open import Data.Unit
open import Data.Product
open import Function using (_∘_)

open import CT

module CwF (C : Category) where

uip : ∀ {A : Set}{x y : A}(p q : x ≡ y) → p ≡ q
uip refl refl = refl

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
A [ σ ]T = record
  { ty = λ γ → ty A (fun σ γ)
  ; mor = λ f {γA} {γB} eq → mor A f (nat σ {f = f} γB ◾ cong (fun σ) eq )
  -- ; id = λ t → cong (λ ξ → mor A C.id ξ t) {!uip !} ◾ id A t
  ; id = λ t → cong₂ (mor A C.id) (uip _ _) refl ◾ id A t
  ; comp = λ f g eq-f eq-g t → {!comp A f g!}
  }

_▶_ : (Γ : Con) → Ty Γ → Con
Γ ▶ t = record
  { pt = λ A → Σ (pt Γ A) (ty t)
  ; mor = λ {A} {B} ϕ (γ , e) → mor Γ ϕ γ , mor t ϕ refl e
  ; id = λ {A} {(γ , e)} → {!cong₂ _,_ (id Γ {A} {γ}) ? !}
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

_[_]t : ∀ {Γ Δ A} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
_[_]t {Γ} {Δ} {A} t σ = record
  { tm = tm t ∘ fun σ
  ; nat = λ f eq → {!!}
  }

var : ∀ {Γ A} → (t : Tm Γ A) → Sub Γ (Γ ▶ A)
var {Γ} t = record
  { fun = λ γ → γ , tm t γ
  ; nat = λ {_} {_} {f} γ → cong (mor Γ f γ ,_) (nat t f refl)
  }

open import TT

ttSyntax : Syntax
ttSyntax = record
  { Con = Con
  ; [] = []
  ; Sub = Sub
  ; Ty = Ty
  ; _▶_ = _▶_
  ; _[_]T = _[_]T
  ; Tm = Tm
  ; _[_]t = _[_]t
  }
