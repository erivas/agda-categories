{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Preordered where

open import Level using (Level; _⊔_; suc)
open import Relation.Binary using (Rel; IsPreorder)

open import Categories.Category using (Category)

open import Categories.Functor using (Functor)
open import Categories.Object.Preordered using (Preordered)

private
  variable
    o o′ ℓ ℓ′ e e′ : Level

module _ {i} (C : Category o ℓ e) (D : Category o′ ℓ′ e′) where
  private
    module C = Category C
    module D = Category D

  record HasPreorder (F : Functor C D) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ suc i) where
    open Functor F

    field
      preord : ∀ X → Preordered {i = i} D (F₀ X)

    infix 4 _⊑_
    _⊑_ : {A : D.Obj} {X : C.Obj} → Rel (A D.⇒ F₀ X) i
    _⊑_ {A} {X} f g = Preordered._⊑_ (preord X) f g

    isPreorder : {A : D.Obj} {X : C.Obj} → IsPreorder (D._≈_ {A} {F₀ X}) (_⊑_ {A} {X})
    isPreorder {A} {X} = Preordered.isPreorder (preord X)

    ∘-resp-⊑ : ∀ {A B X} {f : A D.⇒ B} {g h : B D.⇒ F₀ X} → g ⊑ h → g D.∘ f ⊑ h D.∘ f
    ∘-resp-⊑ {A} {B} {X} {f} {g} {h} ineq = Preordered.∘-resp-⊑ (preord X) ineq

    field
      F-resp-⊑ : ∀ {A B C} {f : A C.⇒ B} {g h : C D.⇒ F₀ A} → g ⊑ h → F₁ f D.∘ g ⊑ F₁ f D.∘ h

  -- preordered functor
  record PreorderedFunctor : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ suc i) where
    field
      F : Functor C D
      hasPreorder : HasPreorder F
    open Functor F public
    open HasPreorder hasPreorder public
