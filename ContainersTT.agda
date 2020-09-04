{-# OPTIONS --type-in-type #-}

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst; inspect; [_])
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

data Resource {Γ} (A : Refinement Γ) (sh : shape Γ) (o : ornament A sh) : Set where
  create : Resource A sh o
  propagate : position A o → Resource A sh o

Is-created : ∀ {Γ} {A : Refinement Γ} {sh o} → Resource A sh o → Set
Is-created create = ⊤
Is-created (propagate _) = ⊥

from-new : ∀ {Γ} {A : Refinement Γ} {sh o} → Source Γ sh A o → Resource A sh o
from-new (old _) = create
from-new (new p) = propagate p

record Reornament {Γ} (A : Refinement Γ) (B : Refinement (refine Γ A)) (sh : shape Γ) : Set where
  field
    reornament : (o : ornament A sh) → ornament B (sh , o)
    reposition : ∀ {o} → position B (reornament o) → Resource A sh o
open Reornament public

-- Proof that there's an output position that isn't filled from a src position
record IsExtension {Γ A B sh} (r : Reornament {Γ} A B sh) : Set where
  constructor isExtension
  field
    src-ornament : ornament A sh
    dest-position : position B (reornament r src-ornament)
    prf : Is-created (reposition r dest-position)
open IsExtension public

Π : ∀ {Γ} → (A : Refinement Γ) → (B : Refinement (refine Γ A)) → Refinement Γ
Π {Γ} A B = record
  { ornament = Reornament A B
  ; position = IsExtension
  }

app : ∀ {Γ A B} → Extension Γ (Π A B) → Extension (refine Γ A) B
decorate (app e) (sh , o) = reornament (decorate e sh) o
reposition (app e) {(sh , o)} p
  with reposition (decorate e sh) p | inspect (reposition (decorate e sh)) p
... | create       | [ eq ] = old (reposition e (isExtension o p (subst Is-created (sym eq) tt)))
... | propagate p₀ | _      = new p₀

lam : ∀ {Γ A B} → Extension (refine Γ A) B → Extension Γ (Π A B)
decorate (lam t) sh = record
  { reornament = decorate t ∘ (sh ,_)
  ; reposition = from-new ∘ reposition t
  }
reposition (lam t) {sh} ext
  with reposition t (dest-position ext) | inspect (reposition t) (dest-position ext)
... | old p | _      = p
... | new p | [ eq ] = case subst Is-created (cong from-new eq) (prf ext) of λ {()}
