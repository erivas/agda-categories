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

module _  (C : Category o ℓ e) (D : Category o′ ℓ′ e′) where
  private
    module C = Category C
    module D = Category D
  open D

  record HasPreorder (F : Functor C D) : Set (levelOfTerm C ⊔ levelOfTerm D) where
    open Functor F

    field
      preord : ∀ X → Preordered D (F₀ X)

    infix 4 _⊑_
    _⊑_ : {A : Obj} {X : C.Obj} → Rel (A ⇒ F₀ X) (ℓ′ ⊔ e′)
    _⊑_ {A} {X} f g = Preordered._⊑_ (preord X) f g

    field
      F-resp-⊑ : ∀ {A B C} {f : A C.⇒ B} {g h : C ⇒ F₀ A} → g ⊑ h → F₁ f ∘ g ⊑ F₁ f ∘ h

  -- preordered functor
  record PreorderedFunctor : Set (levelOfTerm C ⊔ levelOfTerm D) where
    field
      F : Functor C D
      hasPreorder : HasPreorder F
    open Functor F public
    open HasPreorder hasPreorder public
