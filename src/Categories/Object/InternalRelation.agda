{-# OPTIONS --without-K --safe #-}

-- Formalization of internal relations
-- (https://ncatlab.org/nlab/show/internal+relation)

open import Categories.Category.Core using (Category)

module Categories.Object.InternalRelation {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level using (_⊔_; suc)
open import Data.Unit using (⊤)
open import Data.Fin using (Fin; zero) renaming (suc to nzero)
open import Data.Product using (∃; _×_; _,_)

import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR

open import Categories.Diagram.Pullback using (Pullback)
open import Categories.Diagram.KernelPair using (KernelPair)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Object.Preordered renaming (Preordered to ExternallyPreordered)

open import Categories.Category.BinaryProducts 𝒞 using (BinaryProducts; module BinaryProducts)

private
  module 𝒞 = Category 𝒞

open Category 𝒞
open Mor 𝒞 using (JointMono)

-- A relation is a span, "which is (-1)-truncated as a morphism into the cartesian product."
-- (https://ncatlab.org/nlab/show/span#correspondences)
isRelation : {X Y R : 𝒞.Obj} (f : R ⇒ X) (g : R ⇒ Y) → Set (o ⊔ ℓ ⊔ e)
isRelation{X}{Y}{R} f g = JointMono
     (Fin 2)
     (λ{zero → X; (nzero _) → Y})
     (λ{zero → f; (nzero _) → g})

record Relation (X Y : 𝒞.Obj) : Set (suc (o ⊔ ℓ ⊔ e)) where
  constructor rel
  field
    dom : 𝒞.Obj
    p₁ : dom ⇒ X
    p₂ : dom ⇒ Y
    relation : isRelation p₁ p₂

record EqSpan {X R : 𝒞.Obj} (f : R ⇒ X) (g : R ⇒ X) : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
     R×R : Pullback 𝒞 f g

  module R×R = Pullback R×R renaming (P to dom)

  field
     refl  : X ⇒ R
     sym   : R ⇒ R
     trans : R×R.dom ⇒ R

     is-refl₁ : f ∘ refl ≈ id
     is-refl₂ : g ∘ refl ≈ id

     is-sym₁ : f ∘ sym ≈ g
     is-sym₂ : g ∘ sym ≈ f

     is-trans₁ : f ∘ trans ≈ f ∘ R×R.p₂
     is-trans₂ : g ∘ trans ≈ g ∘ R×R.p₁

-- Internal equivalence
-- (=congruences: https://ncatlab.org/nlab/show/congruence)
record Equivalence (X : 𝒞.Obj) : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
     R : Relation X X

  module R = Relation R

  field
    eqspan : EqSpan R.p₁ R.p₂

-- move to properties?

module _ where
  open Pullback hiding (P)
  open 𝒞.Equiv

  -- the span obtained from a KP does need that it forms a pullback
  KP⇒EqSpan : {X Y : 𝒞.Obj} (f : X ⇒ Y) (kp : KernelPair 𝒞 f) (p : Pullback 𝒞 (p₁ kp) (p₂ kp)) → EqSpan (p₁ kp) (p₂ kp)
  KP⇒EqSpan f kp p = record
    { R×R = p
    ; refl  = universal kp refl
    ; sym   = universal kp {_} {p₂ kp}{p₁ kp} (sym (commute kp))
    ; trans = universal kp {_} {p₁ kp ∘ p₂ p}{p₂ kp ∘ p₁ p} f-commute
    ; is-refl₁  = p₁∘universal≈h₁ kp
    ; is-refl₂  = p₂∘universal≈h₂ kp
    ; is-sym₁   = p₁∘universal≈h₁ kp
    ; is-sym₂   = p₂∘universal≈h₂ kp
    ; is-trans₁ = p₁∘universal≈h₁ kp
    ; is-trans₂ = p₂∘universal≈h₂ kp
    }
    where
    open 𝒞.HomReasoning
    open MR 𝒞
    f-commute : f ∘ p₁ kp ∘ p₂ p ≈ f ∘ p₂ kp ∘ p₁ p
    f-commute = begin
      f ∘ p₁ kp ∘ p₂ p   ≈⟨ pullˡ (commute kp) ⟩
      (f ∘ p₂ kp) ∘ p₂ p ≈⟨ pullʳ (sym (commute p)) ⟩
      f ∘ p₁ kp ∘ p₁ p   ≈⟨ pullˡ (commute kp) ⟩
      (f ∘ p₂ kp) ∘ p₁ p ≈⟨ assoc ⟩
      f ∘ p₂ kp ∘ p₁ p   ∎

  -- but the induced relation does not
  KP⇒isRelation : {X Y : 𝒞.Obj} (f : X ⇒ Y) → (kp : KernelPair 𝒞 f) → isRelation (p₁ kp) (p₂ kp)
  KP⇒isRelation f kp _ _ eq = unique-diagram kp (eq zero) (eq (nzero zero))

  KP⇒Relation : {X Y : 𝒞.Obj} (f : X ⇒ Y) → (kp : KernelPair 𝒞 f) → Relation X X
  KP⇒Relation f kp = rel (Pullback.P kp) (p₁ kp) (p₂ kp) (KP⇒isRelation f kp)

  KP⇒Equivalence : {X Y : 𝒞.Obj} (f : X ⇒ Y) → (kp : KernelPair 𝒞 f) (pb : Pullback 𝒞 (p₁ kp) (p₂ kp)) → Equivalence X
  KP⇒Equivalence f kp pb = record { R = KP⇒Relation f kp ; eqspan = KP⇒EqSpan f kp pb }


record PreordSpan {X R : 𝒞.Obj} (f : R ⇒ X) (g : R ⇒ X) : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
     R×R : Pullback 𝒞 f g

  module R×R = Pullback R×R renaming (P to dom)

  field
     refl  : X ⇒ R
     trans : R×R.dom ⇒ R

     is-refl₁ : f ∘ refl ≈ id
     is-refl₂ : g ∘ refl ≈ id

     is-trans₁ : f ∘ trans ≈ f ∘ R×R.p₂
     is-trans₂ : g ∘ trans ≈ g ∘ R×R.p₁

-- Internal Preorder
-- (https://ncatlab.org/nlab/show/preordered+object)
record Preorder (X : 𝒞.Obj) : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
     R : Relation X X

  module R = Relation R

  field
    preordspan : PreordSpan R.p₁ R.p₂


module _ where
  open Pullback hiding (P)
  open 𝒞.Equiv renaming (refl to ≈-refl; trans to ≈-trans)

  -- from an internal preorder we can obtain an external one
  IP⇒EP : {X : 𝒞.Obj} (ipreorder : Preorder X) → ExternallyPreordered 𝒞 X
  IP⇒EP {X} ip = record
    { _⊑_ = λ {A} f g → ∃ (λ p → R.p₁ ∘ p ≈ f × R.p₂ ∘ p ≈ g)
    ; preorder = record
               { isEquivalence = equiv
               ; reflexive = λ { {x} {y} eq →
                                 refl ∘ x
                               , (begin
                                   R.p₁ ∘ refl ∘ x ≈⟨ pullˡ is-refl₁ ⟩
                                   id ∘ x          ≈⟨ identityˡ ⟩
                                   x               ∎)
                               , (begin
                                   R.p₂ ∘ refl ∘ x ≈⟨ pullˡ is-refl₂ ⟩
                                   id ∘ x          ≈⟨ identityˡ ⟩
                                   x               ≈⟨ eq ⟩
                                   y               ∎) }
               ; trans = λ { {i} {j} {k} (l , eqi , eqj₁) (r , eqj₂ , eqk) →
                             trans ∘ universal R×R {_} {r} {l} (≈-trans eqj₂ (sym eqj₁))
                           , (begin
                               R.p₁ ∘ trans ∘ R×R.universal _    ≈⟨ pullˡ is-trans₁ ⟩
                               (R.p₁ ∘ R×R.p₂) ∘ R×R.universal _ ≈⟨ sym (pushʳ (sym (p₂∘universal≈h₂ R×R))) ⟩
                               R.p₁ ∘ l                          ≈⟨ eqi ⟩
                               i                                 ∎)
                           , (begin
                               R.p₂ ∘ trans ∘ R×R.universal _    ≈⟨ pullˡ is-trans₂ ⟩
                               (R.p₂ ∘ R×R.p₁) ∘ R×R.universal _ ≈⟨ sym (pushʳ (sym (p₁∘universal≈h₁ R×R))) ⟩
                               R.p₂ ∘ r                          ≈⟨ eqk ⟩
                               k                                 ∎) }
               }
    ; ∘-resp-⊑ = λ { {_} {_} {f} {g} {h} (p , eqg , eqh) → p ∘ f , pullˡ eqg , pullˡ eqh }
    }
    where
    open 𝒞.HomReasoning
    open MR 𝒞
    open Preorder ip
    open PreordSpan preordspan
