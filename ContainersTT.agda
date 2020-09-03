{-# OPTIONS --type-in-type #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Function using (_∘_; id; flip; const)

open import TT
open import Containers

module _ where

mapR : ∀ {Γ Δ} → Map Γ Δ → Refinement Δ → Refinement Γ
mapR {Γ} {Δ} f R = refinement (ornament R ∘ reshape f) (position R)

mapE : ∀ {Γ Δ R} (f : Map Γ Δ) → (e : Extension Δ R) → Extension Γ (mapR f R)
mapE f e = extension (decorate e ∘ reshape f) (reposition f ∘ reposition e)

coarse : ∀ {Γ Δ R} → Map Γ (refine Δ R) → Map Γ Δ
coarse f = cmap (proj₁ ∘ reshape f) (reposition f ∘ inj₁)

-- TODO: rename
π₂ : ∀ {Γ Δ R}(f : Map Γ (refine Δ R)) → Extension Γ (mapR (coarse f) R)
π₂ f = extension (proj₂ ∘ reshape f) (reposition f ∘ inj₂)

ttSyntax : Syntax
ttSyntax = record
  { Con = Container
  ; Sub = Map
  ; Ty = Refinement
  ; Tm = Extension

  ; [] = con ⊤ λ _ → ⊥
  ; _▶_ = refine

  ; _[_]T = flip mapR
  ; _[_]t = flip mapE
  }
open Syntax ttSyntax

open import Data.Maybe
open import Data.Maybe.Relation.Unary.All

record Reornament {Γ} (A : Refinement Γ) (B : Refinement (refine Γ A)) (sh : shape Γ) : Set where
  field
    reornament : (o : ornament A sh) → ornament B (sh , o)
    reposition : ∀ {o} → position B (reornament o) → Maybe (position A o)
open Reornament public

record IsExtension {Γ A B sh} (r : Reornament {Γ} A B sh) : Set where
  constructor isExtension
  field
    src-ornament : ornament A sh
    dest-position : position B (reornament r src-ornament)
    prf : Is-nothing (reposition r dest-position)
open IsExtension public

Π : ∀ {Γ} → (A : Refinement Γ) → (B : Refinement (refine Γ A)) → Refinement Γ
Π {Γ} A B = record
  { ornament = Reornament A B
  ; position = IsExtension
  }

app : ∀ {Γ A B} → Extension Γ (Π A B) → Extension (refine Γ A) B
app {Γ} {A} {B} e = record
  { decorate = λ (sh , o) → reornament (decorate e sh) o
  ; reposition = λ {(sh , o)} p →
    maybe {B = λ p₀ → p₀ ≡ reposition (decorate e sh) p → position (refine Γ A) (sh , o)}
      (λ p₀ _  → inj₂ p₀)
      (λ    eq → inj₁ (reposition e (isExtension o p (subst Is-nothing eq nothing))))
      (reposition (decorate e sh) p)
      refl
  }

lam : ∀ {Γ A B} → Extension (refine Γ A) B → Extension Γ (Π A B)
lam {Γ} {A} {B} t = record
  { decorate = λ sh → record
    { reornament = λ o → decorate t (sh , o)
    ; reposition = λ p → isInj₂ (reposition t p)
    }
  ; reposition = λ {sh} ext →
    [_,_] {C = λ p → Is-nothing (isInj₂ p) → position Γ sh}
      (λ p _ → p)
      (λ { _ (just ()) })
      (reposition t (dest-position ext))
      (prf ext)
  }
