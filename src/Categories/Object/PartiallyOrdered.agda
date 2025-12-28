{-# OPTIONS --without-K --safe #-}

-- Formalization of external partial orders
-- (https://ncatlab.org/nlab/show/preordered+object)

open import Categories.Category.Core using (Category)

module Categories.Object.PartiallyOrdered {o ℓ e i} (𝒞 : Category o ℓ e) where

open import Level using (_⊔_; suc)
open import Relation.Binary using (Rel; IsPartialOrder; Transitive; Antisymmetric)

private
  module 𝒞 = Category 𝒞

open Category 𝒞
-- "Externally" partially ordered object
record PartiallyOrdered (X : Obj) : Set (o ⊔ ℓ ⊔ e ⊔ suc i) where
  infix 4 _⊑_
  field
    _⊑_ : ∀ {A} → Rel (A ⇒ X) i
  field
    reflexive : ∀ {A} → _≈_ {A} Relation.Binary.⇒ _⊑_
    antisym   : ∀ {A} → Antisymmetric (_≈_ {A}) _⊑_
    trans     : ∀ {A} → Transitive (_⊑_ {A})
    ∘-resp-⊑  : ∀ {A B} {f : A ⇒ B} {g h : B ⇒ X} → g ⊑ h → g ∘ f ⊑ h ∘ f

  isPartialOrder : ∀ {A} → IsPartialOrder (_≈_ {A}) _⊑_
  isPartialOrder {A} = record
    { isPreorder = record
        { isEquivalence = 𝒞.equiv
        ; reflexive = reflexive
        ; trans = trans
        }
    ; antisym = antisym
    }
