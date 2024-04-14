{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Preordered where

open import Level
open import Relation.Binary using (Rel; IsPreorder)

open import Categories.Category

open import Categories.Functor hiding (id)
open import Categories.Object.Preordered

private
  variable
    o o′ ℓ ℓ′ e e′ : Level

module _ {i} (C : Category o ℓ e) (D : Category o′ ℓ′ e′) where
  private
    module C = Category C
    module D = Category D
  open D

  record HasPreorder (F : Functor C D) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ suc i) where
    open Functor F

    field
      preord : ∀ X → Preordered {i = i} D (F₀ X)

    infix 4 _⊑_
    _⊑_ : {A : Obj} {X : C.Obj} → Rel (A ⇒ F₀ X) i
    _⊑_ {A} {X} f g = Preordered._⊑_ (preord X) f g

    isPreorder : {A : Obj} {X : C.Obj} → IsPreorder (_≈_ {A} {F₀ X}) (_⊑_ {A} {X})
    isPreorder {A} {X} = Preordered.isPreorder (preord X)

    ∘-resp-⊑ : ∀ {A B X} {f : A ⇒ B} {g h : B ⇒ F₀ X} → g ⊑ h → g ∘ f ⊑ h ∘ f
    ∘-resp-⊑ {A} {B} {X} {f} {g} {h} ineq = Preordered.∘-resp-⊑ (preord X) ineq

    field
      F-resp-⊑ : ∀ {A B C} {f : A C.⇒ B} {g h : C ⇒ F₀ A} → g ⊑ h → F₁ f ∘ g ⊑ F₁ f ∘ h

  -- preordered functor
  record PreorderedFunctor : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ suc i) where
    field
      F : Functor C D
      hasPreorder : HasPreorder F
    open Functor F public
    open HasPreorder hasPreorder public
