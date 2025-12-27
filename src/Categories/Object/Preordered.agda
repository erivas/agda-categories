{-# OPTIONS --without-K --safe #-}

-- Formalization of external preorders
-- (https://ncatlab.org/nlab/show/preordered+object)

open import Categories.Category.Core using (Category)

module Categories.Object.Preordered {o ℓ e i} (𝒞 : Category o ℓ e) where

open import Level using (Level; _⊔_; suc)
open import Relation.Binary using (Rel; IsPreorder; Transitive; _⇒_)

private
  module 𝒞 = Category 𝒞
-- "Externally" preordered object
record Preordered (X : 𝒞.Obj) : Set (o ⊔ ℓ ⊔ e ⊔ suc i) where
  infix 4 _⊑_
  field
    _⊑_ : ∀ {A} → Rel (A 𝒞.⇒ X) i
  field
    reflexive : ∀ {A} → 𝒞._≈_ {A} ⇒ _⊑_
    trans     : ∀ {A} → Transitive (_⊑_ {A})
    ∘-resp-⊑  : ∀ {A B} {f : A 𝒞.⇒ B} {g h : B 𝒞.⇒ X} → g ⊑ h → g 𝒞.∘ f ⊑ h 𝒞.∘ f

  isPreorder : ∀ {A} → IsPreorder (𝒞._≈_ {A}) _⊑_
  isPreorder {A} = record
    { isEquivalence = 𝒞.equiv
    ; reflexive = reflexive
    ; trans = trans
    }
