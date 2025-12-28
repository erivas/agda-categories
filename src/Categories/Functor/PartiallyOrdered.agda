{-# OPTIONS --without-K --safe #-}

module Categories.Functor.PartiallyOrdered where

open import Level using (Level; _⊔_; suc)
open import Relation.Binary using (Rel; IsPartialOrder)

open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Categories.Object.PartiallyOrdered using (PartiallyOrdered)

private
  variable
    o o′ ℓ ℓ′ e e′ : Level

module _ {i} (C : Category o ℓ e) (D : Category o′ ℓ′ e′) where
  private
    module C = Category C
    module D = Category D

  record HasPartialOrder (F : Functor C D) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ suc i) where
    open Functor F

    field
      partialord : ∀ X → PartiallyOrdered {i = i} D (F₀ X)

    infix 4 _⊑_
    _⊑_ : {A : D.Obj} {X : C.Obj} → Rel (A D.⇒ F₀ X) i
    _⊑_ {A} {X} f g = PartiallyOrdered._⊑_ (partialord X) f g

    isPartialOrder : {A : D.Obj} {X : C.Obj} → IsPartialOrder (D._≈_ {A} {F₀ X}) (_⊑_ {A} {X})
    isPartialOrder {A} {X} = PartiallyOrdered.isPartialOrder (partialord X)

    ∘-resp-⊑ : ∀ {A B X} {f : A D.⇒ B} {g h : B D.⇒ F₀ X} → g ⊑ h → g D.∘ f ⊑ h D.∘ f
    ∘-resp-⊑ {A} {B} {X} {f} {g} {h} ineq = PartiallyOrdered.∘-resp-⊑ (partialord X) ineq

    field
      F-resp-⊑ : ∀ {A B C} {f : A C.⇒ B} {g h : C D.⇒ F₀ A} → g ⊑ h → F₁ f D.∘ g ⊑ F₁ f D.∘ h

  -- partially ordered functor
  record PartiallyOrderedFunctor : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ suc i) where
    field
      F : Functor C D
      hasPartialOrder : HasPartialOrder F
    open Functor F public
    open HasPartialOrder hasPartialOrder public
