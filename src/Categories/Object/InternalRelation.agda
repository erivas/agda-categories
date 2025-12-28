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
open import Categories.Object.PartiallyOrdered renaming (PartiallyOrdered to ExternallyPartiallyOrdered)

open import Categories.Category.BinaryProducts 𝒞 using (BinaryProducts; module BinaryProducts)

private
  module 𝒞 = Category 𝒞

open Category 𝒞
open Mor 𝒞 using (JointMono; Mono)

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


record PreordSpan {X R : 𝒞.Obj} (f : R 𝒞.⇒ X) (g : R 𝒞.⇒ X) : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
     R×R : Pullback 𝒞 f g

  module R×R = Pullback R×R renaming (P to dom)

  field
     refl  : X 𝒞.⇒ R
     trans : R×R.dom 𝒞.⇒ R

     is-refl₁ : f 𝒞.∘ refl 𝒞.≈ 𝒞.id
     is-refl₂ : g 𝒞.∘ refl 𝒞.≈ 𝒞.id

     is-trans₁ : f 𝒞.∘ trans 𝒞.≈ f 𝒞.∘ R×R.p₂
     is-trans₂ : g 𝒞.∘ trans 𝒞.≈ g 𝒞.∘ R×R.p₁

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
  private
    module 𝒞≈ = 𝒞.Equiv

  -- from an internal preorder we can obtain an external one
  IP⇒EP : {X : 𝒞.Obj} (ipreorder : Preorder X) → ExternallyPreordered {i = ℓ ⊔ e} 𝒞 X
  IP⇒EP {X} ip = record
    { _⊑_ = λ {A} f g → ∃ (λ p → R.p₁ 𝒞.∘ p 𝒞.≈ f × R.p₂ 𝒞.∘ p 𝒞.≈ g)
    ; reflexive = λ { {_} {x} {y} eq →
                                 refl 𝒞.∘ x
                               , (begin
                                   R.p₁ 𝒞.∘ refl 𝒞.∘ x ≈⟨ pullˡ is-refl₁ ⟩
                                   𝒞.id 𝒞.∘ x          ≈⟨ identityˡ ⟩
                                   x               ∎)
                               , (begin
                                   R.p₂ 𝒞.∘ refl 𝒞.∘ x ≈⟨ pullˡ is-refl₂ ⟩
                                   𝒞.id 𝒞.∘ x          ≈⟨ identityˡ ⟩
                                   x               ≈⟨ eq ⟩
                                   y               ∎) }
    ; trans = λ { {_} {i} {j} {k} (l , eqi , eqj₁) (r , eqj₂ , eqk) →
                             trans 𝒞.∘ universal R×R {_} {r} {l} (𝒞≈.trans eqj₂ (𝒞≈.sym eqj₁))
                           , (begin
                               R.p₁ 𝒞.∘ trans 𝒞.∘ R×R.universal _    ≈⟨ pullˡ is-trans₁ ⟩
                               (R.p₁ 𝒞.∘ R×R.p₂) 𝒞.∘ R×R.universal _ ≈⟨ pullʳ (p₂∘universal≈h₂ R×R) ⟩
                               R.p₁ 𝒞.∘ l                          ≈⟨ eqi ⟩
                               i                                 ∎)
                           , (begin
                               R.p₂ 𝒞.∘ trans 𝒞.∘ R×R.universal _    ≈⟨ pullˡ is-trans₂ ⟩
                               (R.p₂ 𝒞.∘ R×R.p₁) 𝒞.∘ R×R.universal _ ≈⟨ pullʳ (p₁∘universal≈h₁ R×R) ⟩
                               R.p₂ 𝒞.∘ r                          ≈⟨ eqk ⟩
                               k                                 ∎) }
    ; ∘-resp-⊑ = λ { {_} {_} {f} {g} {h} (p , eqg , eqh) → p 𝒞.∘ f , pullˡ eqg , pullˡ eqh }
    }
    where
    open 𝒞.HomReasoning
    open MR 𝒞
    open Preorder ip
    open PreordSpan preordspan


record PartialordSpan {X R : 𝒞.Obj} (f : R 𝒞.⇒ X) (g : R 𝒞.⇒ X) : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
     R×R : Pullback 𝒞 f g
     R×Rᵒ : Pullback 𝒞 g f

  module R×R = Pullback R×R renaming (P to dom)
  module R×Rᵒ = Pullback R×Rᵒ renaming (P to dom)

  field
     refl  : X 𝒞.⇒ R
     trans : R×R.dom 𝒞.⇒ R
     antisym : R×Rᵒ.dom 𝒞.⇒ X

     is-refl₁ : f 𝒞.∘ refl 𝒞.≈ 𝒞.id
     is-refl₂ : g 𝒞.∘ refl 𝒞.≈ 𝒞.id

     is-trans₁ : f 𝒞.∘ trans 𝒞.≈ f 𝒞.∘ R×R.p₂
     is-trans₂ : g 𝒞.∘ trans 𝒞.≈ g 𝒞.∘ R×R.p₁

     is-antisym-1 : f 𝒞.∘ R×Rᵒ.p₁ 𝒞.≈ antisym
     is-antisym-mid : g 𝒞.∘ R×Rᵒ.p₁ 𝒞.≈ antisym
     is-antisym-2 : g 𝒞.∘ R×Rᵒ.p₂ 𝒞.≈ antisym

-- Internal Partial Order
-- (https://ncatlab.org/nlab/show/partially+ordered+object)
record PartialOrder (X : 𝒞.Obj) : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
     R : Relation X X

  module R = Relation R

  field
    partialordspan : PartialordSpan R.p₁ R.p₂


module _ where
  open Pullback hiding (P)
  private
    module 𝒞≈ = 𝒞.Equiv

  -- from an internal partial order we can obtain an external one
  IPO⇒EPO : {X : 𝒞.Obj} (ipartialorder : PartialOrder X) → ExternallyPartiallyOrdered {i = ℓ ⊔ e} 𝒞 X
  IPO⇒EPO {X} ipo = let module IPO = PartialOrder ipo
                        open IPO using (R; partialordspan)
                        module R = Relation R
                        module POS = PartialordSpan partialordspan
                        open MR 𝒞
                    in record
    { _⊑_ = λ {A} f g → ∃ (λ p → R.p₁ 𝒞.∘ p 𝒞.≈ f × R.p₂ 𝒞.∘ p 𝒞.≈ g)
    ; reflexive = λ { {_} {x} {y} eq →
                                 let open 𝒞.HomReasoning
                                 in POS.refl 𝒞.∘ x
                               , (begin
                                   R.p₁ 𝒞.∘ POS.refl 𝒞.∘ x ≈⟨ pullˡ POS.is-refl₁ ⟩
                                   𝒞.id 𝒞.∘ x          ≈⟨ identityˡ ⟩
                                   x               ∎)
                               , (begin
                                   R.p₂ 𝒞.∘ POS.refl 𝒞.∘ x ≈⟨ pullˡ POS.is-refl₂ ⟩
                                   𝒞.id 𝒞.∘ x          ≈⟨ identityˡ ⟩
                                   x               ≈⟨ eq ⟩
                                   y               ∎) }
    ; antisym = λ { {_} {i} {j} (f , eqi₁ , eqj₁) (g , eqj₂ , eqi₂) →
                             let open 𝒞.HomReasoning
                                 comm = 𝒞≈.trans eqj₁ (𝒞≈.sym eqj₂)
                                 u = universal POS.R×Rᵒ {_} {f} {g} comm
                             in begin
                               i                                     ≈˘⟨ eqi₁ ⟩
                               R.p₁ 𝒞.∘ f                            ≈˘⟨ refl⟩∘⟨ p₁∘universal≈h₁ POS.R×Rᵒ ⟩
                               R.p₁ 𝒞.∘ Pullback.p₁ POS.R×Rᵒ 𝒞.∘ u   ≈⟨ pullˡ POS.is-antisym-1 ⟩
                               POS.antisym 𝒞.∘ u                      ≈˘⟨ pullˡ POS.is-antisym-mid ⟩
                               (R.p₂ 𝒞.∘ Pullback.p₁ POS.R×Rᵒ) 𝒞.∘ u  ≈⟨ pullʳ (p₁∘universal≈h₁ POS.R×Rᵒ) ⟩
                               R.p₂ 𝒞.∘ f                            ≈⟨ eqj₁ ⟩
                               j                                     ∎ }
    ; trans = λ { {_} {i} {j} {k} (l , eqi , eqj₁) (r , eqj₂ , eqk) →
                             let open 𝒞.HomReasoning in
                             POS.trans 𝒞.∘ universal POS.R×R {_} {r} {l} (𝒞≈.trans eqj₂ (𝒞≈.sym eqj₁))
                           , (begin
                               R.p₁ 𝒞.∘ POS.trans 𝒞.∘ universal POS.R×R _ ≈⟨ pullˡ POS.is-trans₁ ⟩
                               (R.p₁ 𝒞.∘ Pullback.p₂ POS.R×R) 𝒞.∘ universal POS.R×R _ ≈⟨ pullʳ (p₂∘universal≈h₂ POS.R×R) ⟩
                               R.p₁ 𝒞.∘ l                          ≈⟨ eqi ⟩
                               i                                 ∎)
                           , (begin
                               R.p₂ 𝒞.∘ POS.trans 𝒞.∘ universal POS.R×R _    ≈⟨ pullˡ POS.is-trans₂ ⟩
                               (R.p₂ 𝒞.∘ Pullback.p₁ POS.R×R) 𝒞.∘ universal POS.R×R _ ≈⟨ pullʳ (p₁∘universal≈h₁ POS.R×R) ⟩
                               R.p₂ 𝒞.∘ r                          ≈⟨ eqk ⟩
                               k                                 ∎) }
    ; ∘-resp-⊑ = λ { {_} {_} {f} {g} {h} (p , eqg , eqh) → p 𝒞.∘ f , pullˡ eqg , pullˡ eqh }
    }
