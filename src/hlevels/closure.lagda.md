---
title: "h-Levels: Closure"
description: "Voevodsky's notion of h-levels of a type. Level n implies level m, if n ≤ m, and similar properties"
---

```agda
{-# OPTIONS --without-K --safe --exact-split #-}

module hlevels.closure where

open import level
open import mltt
open import types.naturals.core
open import types.naturals.order
open import homotopy.retraction
open import function.homotopyequivalence
open import hlevels.core

open ≡-Reasoning
open ◾-lemmas
```

### h-Levels are upper closed

```agda
hlevel-upper : ∀ {ℓ} (n : ℕ) {A : Set ℓ} → A isofhlevel n → A isofhlevel (suc n)
hlevel-upper zero {A} l = λ x y → inhabited-prop→singleton (p x y) (s x y)
  where
    p : is-prop A
    p = singleton→prop l

    s : is-set A
    s = prop→set p

hlevel-upper (suc n) {A} l = λ x y → hlevel-upper n (l x y)
```

In [UniMath][UniMath] this becomes:

```agda
hlevelntosn = hlevel-upper
```

```agda
hlevel-≤ : ∀ {ℓ} {A : Set ℓ} {m n : ℕ} →
           m ≤ n → A isofhlevel m → A isofhlevel n
hlevel-≤ {m = .0} {zero} z≤n hA = hA
hlevel-≤ {m = .0} {suc n} z≤n hA = hlevel-upper n (hlevel-≤ {n = n} z≤n hA)
hlevel-≤ {m = .(suc _)} {suc n} (s≤s m≤n) hA = λ x y → hlevel-≤ m≤n (hA x y)
```

### Retractions

Retractions preserve levels. The base case, that of a contractible
type, is useful on its own.

```agda

singleton-retract : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} →
                    A ◅ B → is-singleton B → is-singleton A
singleton-retract record { retr = r ; sect = s ; homot = h } ib = r (center ib) , γ
  where
    φ = centrality ib
    γ : (a : domain s) → r (center ib) ≡ a
    γ a = begin 
          r (center ib) ≡⟨ ap r (φ (s a))  ⟩
          r (s a)       ≡⟨ h a ⟩
          a ∎

hlevel-retract : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {n : ℕ} →
                 A ◅ B → B isofhlevel n → A isofhlevel n
hlevel-retract {n = zero} r is = singleton-retract r is
hlevel-retract {n = suc n} rAB is x y = hlevel-retract ρ (is (s x) (s y))
  where
    open _◅_
    r = retr rAB
    s = sect rAB
    h = homot rAB
    ρ : (x ≡ y) ◅ (s x ≡ s y)
    ρ = record { retr = r' ; sect = s' ; homot = h' }
      where
        r' : s x ≡ s y → x ≡ y
        r' = λ p → (h x) ⁻¹ ◾ ( ap r p  ◾ h y)
        s' : x ≡ y → s x ≡ s y
        s' = ap s
        h' : r' ∘′ s' ~ id
        h' refl = (linv (h x) ⁻¹) ⁻¹
```

Similarly, for isomorphisms or homotopy equivalences:

```agda
hlevel-iso : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {n : ℕ} →
             A ≅ B → A isofhlevel n → B isofhlevel n
hlevel-iso {n = n} (hoeq to from ε η) hA =
           hlevel-retract (record { retr = to ; sect = from ; homot = ε }) hA
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---

[UniMath]: https://github.com/UniMath/UniMath
