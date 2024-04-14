{-# OPTIONS --without-K --safe #-}

-- Define Preordered Monad

module Categories.Monad.Preordered  where

open import Level
open import Relation.Binary using (IsPreorder)

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Functor
open import Categories.NaturalTransformation hiding (id)
open import Categories.Monad hiding (id)
open import Categories.Functor.Preordered
open import Categories.Functor.Monoidal
open import Categories.Category.Construction.Kleisli

private
  variable
    o ℓ e i : Level

-- preorder on a monad

record Preorder {C : Category o ℓ e} (M : Monad C) : Set (o ⊔ ℓ ⊔ e ⊔ suc i) where
  open Category C
  private
    module M = Monad M
  open M using (F)
  open NaturalTransformation M.η using (η)
  open NaturalTransformation M.μ renaming (η to μ)
  open Functor F
  field
    hasPreorder : HasPreorder {i = i} _ _ F
  open HasPreorder hasPreorder public

  field
    μ-⊑ : ∀ {A B} {f g : A ⇒ F₀ (F₀ B)} → f ⊑ g → μ _ ∘ f ⊑ μ _ ∘ g
    μ-F-⊑ : ∀ {A B} {f g : A ⇒ F₀ B} → f ⊑ g → μ _ ∘ F₁ f ⊑ μ _ ∘ F₁ g

record PreorderedMonad {C : Category o ℓ e} : Set (o ⊔ ℓ ⊔ e ⊔ suc i) where
  field
    M        : Monad C
    preorder : Preorder {i = i} M

  module M = Monad M
  open Preorder preorder public


module _ {C : Category o ℓ e} (PM : PreorderedMonad {i = i} {C = C}) where
  open Category C
  open PreorderedMonad PM
  private
    module Kl = Category (Kleisli M)

  PreorderedMonad⇒KleisliEnrichmentˡ : ∀ {A B C} {f g : B Kl.⇒ C} {h : A Kl.⇒ B} → f ⊑ g → f Kl.∘ h ⊑ g Kl.∘ h
  PreorderedMonad⇒KleisliEnrichmentˡ f⊑g = ∘-resp-⊑ (μ-F-⊑ f⊑g)

  PreorderedMonad⇒KleisliEnrichmentʳ : ∀ {A B C} {f : B Kl.⇒ C} {g h : A Kl.⇒ B} → g ⊑ h → f Kl.∘ g ⊑ f Kl.∘ h
  PreorderedMonad⇒KleisliEnrichmentʳ {A} {B} {C} {f} {g} {h} f⊑g = trans (reflexive assoc) (trans (μ-⊑ (F-resp-⊑ f⊑g)) (reflexive sym-assoc))
    where open IsPreorder (isPreorder {A} {C})
