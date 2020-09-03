{-# OPTIONS --type-in-type #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Relation.Nullary
open import Function using (_∘_; id; flip; const; case_of_)

open import TT
open import Containers

module _ where

mapR : ∀ {Γ Δ} → Map Γ Δ → Refinement Δ → Refinement Γ
mapR {Γ} {Δ} f R = refinement (ornament R ∘ reshape f) (position R)

mapE : ∀ {Γ Δ R} (f : Map Γ Δ) → (e : Extension Δ R) → Extension Γ (mapR f R)
mapE f e = extension (decorate e ∘ reshape f) (reposition f ∘ reposition e)

coarse : ∀ {Γ Δ R} → Map Γ (refine Δ R) → Map Γ Δ
coarse f = cmap (proj₁ ∘ reshape f) (reposition f ∘ old)

-- TODO: rename
π₂ : ∀ {Γ Δ R}(f : Map Γ (refine Δ R)) → Extension Γ (mapR (coarse f) R)
π₂ f = extension (proj₂ ∘ reshape f) (reposition f ∘ new)

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

open import Data.Maybe.Relation.Unary.All

data Resource {Γ Δ} (A : Refinement Γ) (B : Refinement Δ) (sh : shape Γ) (o : ornament A sh) : Set where
  create : Resource A B sh o
  propagate : position A o → Resource A B sh o

record Reornament {Γ} (A : Refinement Γ) (B : Refinement (refine Γ A)) (sh : shape Γ) : Set where
  field
    reornament : (o : ornament A sh) → ornament B (sh , o)
    reposition : ∀ {o} → position B (reornament o) → Maybe (position A o)
open Reornament public

-- Proof that there's a new position that isn't filled from a src position
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
  ; reposition = reposition′
  }
  where
    decorate′ : (sh : shape (refine Γ A)) → ornament B sh
    decorate′ (sh , o) = reornament (decorate e sh) o

    reposition′ : ∀ {sh} →
      position           B  (decorate′ sh) →
      position (refine Γ A)            sh
    reposition′ {(sh , o)} p = case reposition (decorate e sh) p of λ where
      nothing → old (reposition e (isExtension o p {!!}))
      (just p₀) → new p₀
      -- maybe {B = λ p₀ → p₀ ≡ mp₀ → position (refine Γ A) (sh , o)}
      --   (λ p₀ _  → new p₀)
      --   (λ    eq → old (reposition e (isExtension o p (subst Is-nothing eq nothing))))
      --   mp₀
      --   refl
      -- where
      --   mp₀ = reposition (decorate e sh) p

lam : ∀ {Γ A B} → Extension (refine Γ A) B → Extension Γ (Π A B)
lam {Γ} {A} {B} t = record
  { decorate = λ sh → record
    { reornament = λ o → decorate t (sh , o)
    ; reposition = λ p → from-new (reposition t p)
    }
  ; reposition = λ {sh} ext → {!!}
    -- [_,_] {C = λ p → Is-nothing (from-new p) → position Γ sh}
    --   (λ p _ → p)
    --   (λ { _ (just ()) })
    --   (reposition t (dest-position ext))
    --   (prf ext)
  }
