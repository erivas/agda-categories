{-# OPTIONS --without-K --safe #-}

-- Formalization of external preorders
-- (https://ncatlab.org/nlab/show/preordered+object)

open import Categories.Category.Core using (Category)

module Categories.Object.Preordered {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level using (_⊔_; suc)
open import Relation.Binary using (Rel; IsPreorder)

private
  module 𝒞 = Category 𝒞

open Category 𝒞

-- "Externally" preordered object
record Preordered (X : Obj) : Set (suc (o ⊔ ℓ ⊔ e)) where
  infix 4 _⊑_
  field
    _⊑_ : ∀ {A} → Rel (A ⇒ X) (ℓ ⊔ e)
  field
    isPreorder : ∀ {A} → IsPreorder (_≈_ {A} {X}) (_⊑_ {A})
    ∘-resp-⊑ : ∀ {A B} {f : A ⇒ B} {g h : B ⇒ X} → g ⊑ h → g ∘ f ⊑ h ∘ f
