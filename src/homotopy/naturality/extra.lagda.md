---
title: "Naturality"
description: "Naturality constructions: additional statements about pointwise function homotopies"
---

```agda
{-# OPTIONS --without-K --safe #-}

module homotopy.naturality.extra where

open import level
open import function.core
open import function.pointwise
open import mltt.identity
--open import mltt.sigma
--open import mltt.pi
open import homotopy.twocatconstructions
open import homotopy.naturality.core

open ◾-lemmas
open ap-lemmas
open ≡-Reasoning
```

This is here for want of a better place.
But somehow it does not feel right in the `core` module.

```agda
corollary[homot-natural] : ∀ {ℓ} {A : Set ℓ} {f : A → A} (h : f ~ id) {x : A} → (h (f x)) ≡ (ap f (h x))
corollary[homot-natural]  {f = f} h {x} = h (f x) ≡⟨ (ru _ ) ⁻¹ ⟩
                                          h (f x) ◾ (idp (f x))            ≡⟨ first ⁻¹ ⟩
                                          h (f x) ◾ ((h x) ◾ (h x) ⁻¹)     ≡⟨ second ⁻¹ ⟩ 
                                          (h (f x) ◾ (h x)) ◾ (h x) ⁻¹     ≡⟨ third ⟩
                                          (h (f x) ◾ ap id (h x)) ◾ h x ⁻¹ ≡⟨ fourth ⟩
                                          (ap f (h x) ◾ (h x)) ◾ (h x) ⁻¹  ≡⟨ fifth ⟩
                                          ap f (h x) ◾ (h x ◾ h x ⁻¹)      ≡⟨ sixth ⟩
                                          ap f (h x) ◾ idp (lhs (h x))     ≡⟨ ru _  ⟩
                                          ap f (h x) ∎
                                            where
                                              first = (h (f x)) ◾ˡ (rinv (h x))
                                              second = assoc (h (f x)) (h x) ((h x) ⁻¹)
                                              third = (h (f x) ◾ˡ (apid (h x)) ⁻¹) ◾ʳ (h x) ⁻¹
                                              fourth = (homot-natural h (h x)) ◾ʳ (h x) ⁻¹
                                              fifth = (assoc (ap f (h x)) (h x) (h x ⁻¹))
                                              sixth = (ap f (h x) ◾ˡ rinv (h x))


-- also with the whiskering lemmas
corollary[homot-natural]' : ∀ {ℓ} {A : Set ℓ} {f : A → A} (h : f ~ id) {x : A} → (h (f x)) ≡ (ap f (h x))
corollary[homot-natural]'  {f = f} h {x} = i ◾⁻ʳ (h x)
                                           where
                                             i = h (f x) ◾ (h x)         ≡⟨ ( h (f x) ◾ˡ (apid (h x)) )⁻¹ ⟩
                                                 h (f x) ◾ (ap id (h x)) ≡⟨ homot-natural h (h x) ⟩
                                                 ((ap f (h x)) ◾ (h x))  ∎
```
