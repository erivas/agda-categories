{-# OPTIONS --without-K --safe #-}

-- Define Partially Ordered Monad

module Categories.Monad.PartiallyOrdered where

open import Level using (Level; _⊔_; suc)
open import Relation.Binary using (IsPartialOrder)

open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Monad using (Monad)
open import Categories.Functor.PartiallyOrdered using (HasPartialOrder)
open import Categories.Category.Construction.Kleisli using (Kleisli)

private
  variable
    o ℓ e i : Level

-- partial order on a monad

record Preorder {C : Category o ℓ e} (M : Monad C) : Set (o ⊔ ℓ ⊔ e ⊔ suc i) where
  open Category C
  private
    module M = Monad M
  open M using (F)
  open NaturalTransformation M.η using (η)
  open NaturalTransformation M.μ renaming (η to μ)
  open Functor F
  field
    hasPartialOrder : HasPartialOrder {i = i} _ _ F
  open HasPartialOrder hasPartialOrder public

  field
    μ-⊑ : ∀ {A B} {f g : A ⇒ F₀ (F₀ B)} → f ⊑ g → μ _ ∘ f ⊑ μ _ ∘ g
    μ-F-⊑ : ∀ {A B} {f g : A ⇒ F₀ B} → f ⊑ g → μ _ ∘ F₁ f ⊑ μ _ ∘ F₁ g

record PartiallyOrderedMonad {C : Category o ℓ e} : Set (o ⊔ ℓ ⊔ e ⊔ suc i) where
  field
    M        : Monad C
    preorder : Preorder {i = i} M

  module M = Monad M
  open Preorder preorder public


module _ {C : Category o ℓ e} (PM : PartiallyOrderedMonad {i = i} {C = C}) where
  open Category C
  open PartiallyOrderedMonad PM
  private
    module Kl = Category (Kleisli M)

  PartiallyOrderedMonad⇒KleisliEnrichmentˡ : ∀ {A B C} {f g : B Kl.⇒ C} {h : A Kl.⇒ B} → f ⊑ g → f Kl.∘ h ⊑ g Kl.∘ h
  PartiallyOrderedMonad⇒KleisliEnrichmentˡ f⊑g = ∘-resp-⊑ (μ-F-⊑ f⊑g)

  PartiallyOrderedMonad⇒KleisliEnrichmentʳ : ∀ {A B C} {f : B Kl.⇒ C} {g h : A Kl.⇒ B} → g ⊑ h → f Kl.∘ g ⊑ f Kl.∘ h
  PartiallyOrderedMonad⇒KleisliEnrichmentʳ {A} {B} {C} {f} {g} {h} f⊑g = trans (reflexive assoc) (trans (μ-⊑ (F-resp-⊑ f⊑g)) (reflexive sym-assoc))
    where open IsPartialOrder (isPartialOrder {A} {C})
