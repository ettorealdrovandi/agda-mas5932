---
title: "2-categorical constructions"
description: "Interchange law for vertical and horizontal compositions of 2-cells"
---

--------------------------------------------------

```agda
{-# OPTIONS --without-K --safe #-}

module homotopy.twocatconstructions.interchange where

open import level
open import mltt.identity
open import homotopy.twocatconstructions.core
open import homotopy.twocatconstructions.pathlib


open ≡-Reasoning
open ◾-lemmas
open ap-lemmas
```

```agda
module _ {ℓ : Level} {A : Set ℓ} {x y z : A} where

  interchange : {p q r : x ≡ y} {u v w : y ≡ z}
                (α : p ≡ q) (β : q ≡ r) (γ : u ≡ v) (δ : v ≡ w) →
                (α ◾ β) ★ (γ ◾ δ) ≡ (α ★ γ) ◾ (β ★ δ)
  interchange {q = q} {r} {u} {v} α β γ δ =
              (α ◾ β) ★ (γ ◾ δ)                             ≡⟨ refl ⟩
              ((α ◾ β) ◾ʳ u) ◾ (r ◾ˡ (γ ◾ δ))               ≡⟨ (α ◾ᵥ β ◾ʳ u) ◾ʳ (r ◾ˡ (γ ◾ δ))              ⟩
              ((α ◾ʳ u) ◾ (β ◾ʳ u)) ◾ (r ◾ˡ (γ ◾ δ))        ≡⟨ ((α ◾ʳ u) ◾ (β ◾ʳ u)) ◾ˡ (r ◾ˡ γ ◾ᵥ δ)       ⟩
              ((α ◾ʳ u) ◾ (β ◾ʳ u)) ◾ ((r ◾ˡ γ) ◾ (r ◾ˡ δ)) ≡⟨ path-rewrite (α ◾ʳ u) (★-is-★′ β γ) (r ◾ˡ δ) ⟩
              ((α ◾ʳ u) ◾ (q ◾ˡ γ)) ◾ ((β ◾ʳ v) ◾ (r ◾ˡ δ)) ≡⟨ refl ⟩ 
              (α ★ γ) ◾ (β ★ δ) ∎

  interchange′ : {p q r : x ≡ y} {u v w : y ≡ z}
                 (α : p ≡ q) (β : q ≡ r) (γ : u ≡ v) (δ : v ≡ w) →
                 (α ◾ β) ★′ (γ ◾ δ) ≡ (α ★′ γ) ◾ (β ★′ δ)
  interchange′ α β γ δ = (α ◾ β) ★′ (γ ◾ δ)           ≡⟨  ( ★-is-★′ (α ◾ β) (γ ◾ δ) ) ⁻¹ ⟩
                         (α ◾ β) ★ (γ ◾ δ)            ≡⟨ interchange α β γ δ ⟩
                         (α ★ γ) ◾ (β ★ δ)            ≡⟨ (★-is-★′ α γ) ◾ʳ (β ★ δ) ⟩
                         (α ★′ γ) ◾ (β ★ δ)           ≡⟨ (α ★′ γ) ◾ˡ (★-is-★′ β δ) ⟩
                         (α ★′ γ) ◾ (β ★′ δ) ∎
```
