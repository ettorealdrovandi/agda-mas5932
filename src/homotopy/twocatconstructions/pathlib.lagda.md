---
title: "2-categorical constructions"
description: "PathLib: utilities to manipulate path concatenations"
---

--------------------------------------------------

```agda
{-# OPTIONS --without-K --safe #-}

module homotopy.twocatconstructions.pathlib where

open import level
open import mltt.identity
open import homotopy.twocatconstructions.core


open ≡-Reasoning
open ◾-lemmas
open ap-lemmas
```

The following combination occurs often:

Consider two path concatenations of the form

```agda-ignore

     p   q   r   s
   x → y → z → w → t 

   and

     p   r'   q'  s
   x → y → z' → w → t
  
   with η : q ◾ r ≡ r' ◾ q'

   rewrite: 

   (p ◾ q) ◾ (r ◾ s) ≡ (p ◾ r') ◾ (q' ◾ s)
```

```agda
module _ {ℓ : Level} {A : Set ℓ} {x y z w t : A} where

  path-rewrite : {z' : A} (p : x ≡ y) {q : y ≡ z} {r : z ≡ w} {r' : y ≡ z'} {q' : z' ≡ w}
                 (η : q ◾ r ≡ r' ◾ q') (s : w ≡ t) → (p ◾ q) ◾ (r ◾ s) ≡ (p ◾ r') ◾ (q' ◾ s)
  path-rewrite p {q} {r} {r'} {q'} η s = (p ◾ q) ◾ (r ◾ s) ≡⟨ assoc p q (r ◾ s) ⟩
                                         p ◾ (q ◾ (r ◾ s)) ≡⟨ ap (λ u → p ◾ u) ((assoc q r s) ⁻¹) ⟩
                                         p ◾ ((q ◾ r) ◾ s) ≡⟨ p ◾ˡ (η ◾ʳ s) ⟩
                                         p ◾ ((r' ◾ q') ◾ s) ≡⟨ ap (λ u → p ◾ u) (assoc r' q' s) ⟩
                                         p ◾ (r' ◾ (q' ◾ s)) ≡⟨ (assoc p r' (q' ◾ s)) ⁻¹ ⟩
                                         (p ◾ r') ◾ (q' ◾ s) ∎

```

