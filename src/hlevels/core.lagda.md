---
title: "h-Levels: Core"
description: "Voevodsky's notion of h-levels of a type. Main definitions"
---

### Contents (#top)

1. [h Levels](#hlevels)
1. [Singletons, Propositions, and Sets](#singl-props-sets)
1. [Propositions are of h-level 1](#props-h1)
1. [Sets are of h-level 2](#sets-h2)

--------------------------------------------------

```agda
{-# OPTIONS --without-K --safe --exact-split #-}

module hlevels.core where

open import level
open import mltt
open import types.naturals.core
open import homotopy.twocatconstructions


open ≡-Reasoning
open ◾-lemmas
```

### h Levels {#hlevels}

It is convenient to have both names `h` and `_isofhlevel_`
```agda
hlevel : ∀ {ℓ} → ℕ → Set ℓ → Set ℓ
hlevel zero A = Σ A (λ c → (a : A) → c ≡ a)
hlevel (suc n) A = (x y : A) → hlevel n (x ≡ y)

_isofhlevel_ : ∀{ℓ} → Set ℓ → ℕ → Set ℓ
A isofhlevel n = hlevel n A
```

### Singletons, Propositions, and Sets {#singl-props-sets}

```agda
iscontr isContr is-contr isSingleton is-singleton : ∀ {ℓ} → Set ℓ → Set ℓ
iscontr = hlevel 0
isContr = iscontr
is-contr = iscontr
isSingleton = iscontr
is-singleton = iscontr

center : ∀ {ℓ} {A : Set ℓ} → is-singleton A → A
center is = π₁ is

centrality : ∀ {ℓ} {A : Set ℓ} (is : is-singleton A) →
             (a : A) → center is ≡ a
centrality is = λ a → π₂ is a
```

```agda
isProp : ∀ {ℓ} → Set ℓ → Set ℓ
isProp A = (x y : A) → x ≡ y

ispathconn isprop is-prop : ∀ {ℓ} → Set ℓ → Set ℓ
ispathconn = isProp
isprop = isProp
is-prop = isProp
```

```agda
singleton→prop : ∀ {ℓ} {A : Set ℓ} → is-singleton A → is-prop A
singleton→prop is = λ x y → x ≡⟨ (γ x) ⁻¹ ⟩
                            c ≡⟨ γ y ⟩
                            y ∎
  where
    c = π₁ is
    γ = π₂ is

inhabited-prop→singleton : ∀ {ℓ} {A : Set ℓ} → A → is-prop A → is-singleton A
inhabited-prop→singleton a is = a , (is a)
```

```agda
isSet : ∀ {ℓ} → Set ℓ → Set ℓ
isSet A = (x y : A) → isProp (x ≡ y)

isSet' is-set is-set' : ∀ {ℓ} → Set ℓ → Set ℓ
isSet' = isSet
is-set = isSet
is-set' = isSet

-- FIXME: This is for compatibility, but it will (should) go away
isSet→isSet' : ∀ {ℓ} (A : Set ℓ) → isSet A → isSet' A
isSet→isSet' A = id

isSet'→isSet : ∀ {ℓ} (A : Set ℓ) → isSet' A → isSet A
isSet'→isSet A = id
```

The following is from the HoTT book, showing that propositions are sets.
```agda
prop→set : ∀ {ℓ} {A : Set ℓ} → is-prop A → is-set A
prop→set {ℓ} {A} is x y p q = p                   ≡⟨ linv (g {x} x) ⁻¹ ◾ʳ p ⟩
                              (g x ⁻¹ ◾ g x) ◾ p ≡⟨ assoc (g x ⁻¹) _ _ ⟩
                              g x ⁻¹ ◾ (g x ◾ p) ≡⟨ g x ⁻¹ ◾ˡ k p ⟩
                              g x ⁻¹ ◾ g y       ≡⟨  g x ⁻¹ ◾ˡ (k q) ⁻¹ ⟩
                              g x ⁻¹ ◾ (g x ◾ q) ≡⟨ (assoc (g x ⁻¹) _ _) ⁻¹ ⟩
                              (g x ⁻¹ ◾ g x) ◾ q ≡⟨ linv (g x) ◾ʳ q ⟩
                              q ∎
  where
    g : {x : A} (y : A) → (x ≡ y)
    g {x} y = is x y

    h : {x : A} {y z : A} (p : y ≡ z) →
        transport (λ v → x ≡ v) p (g y) ≡ g z
    h {x} {y} {z} p = apd g p

    k : {x : A} {y z : A} (p : y ≡ z) →
        (g {x} y) ◾ p ≡ g z
    k {x} {y} {z} p = (g {x} y) ◾ p ≡⟨  (transport-path-f p (g y)) ⁻¹ ⟩
                      transport (λ v → x ≡ v) p (g y) ≡⟨ h p ⟩
                      g z ∎
      where
        open transport-in-paths
```

### Propositions are of h-level 1 {#props-h1}

```agda
prop→hlevel1 : ∀ {ℓ} {A : Set ℓ} → is-prop A → A isofhlevel 1
prop→hlevel1 {ℓ} {A} is = λ x y → inhabited-prop→singleton (is x y) (s x y)
  where
    s : is-set A
    s = prop→set is

hlevel1→prop : ∀ {ℓ} {A : Set ℓ} → A isofhlevel 1 → is-prop A
hlevel1→prop {ℓ} {A} is = λ x y → center {A = (x ≡ y)} (is x y)
```

### Sets are of h-level 2 {#sets-h2}

```agda
set→hlevel2 : ∀ {ℓ} {A : Set ℓ} → is-set A → A isofhlevel 2
set→hlevel2 is = λ x y → prop→hlevel1 (is x y)

hlevel2→set : ∀ {ℓ} {A : Set ℓ} → A isofhlevel 2 → is-set A
hlevel2→set {ℓ} {A} is = λ x y → hlevel1→prop (is x y) 
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---
