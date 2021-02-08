---
title: "Sigma types"
subtitle: "Martin-Löf Type Theory"
description: "A minimal Type Theory in Martin-Löf style: Sigma types"
---

1. [Σ-Types](#sigma)
   1. [Induction and recursion principles](#indrec)
1. [Cartesian Products](#cartesian)
   1. [Induction and recursion principles](#indreccart)
   1. [Universal properties](#universal_cart_sigma)

--------------------------------------------------------------------------------

```agda
{-# OPTIONS --without-K --safe #-}

module mltt.sigma where

open import level renaming (zero to lzero; suc to lsuc) public
```

### Σ-Types {#sigma}

Instead of
    data Σ {ℓ ℓ'} (B : Set ℓ) (E : B → Set ℓ') : Set (ℓ ⊔ ℓ') where
      _,_ : (b : B) (e : E b) → Σ B E

define as a record:

```agda
record Σ {ℓ ℓ'} (B : Set ℓ) (E : B → Set ℓ') : Set (ℓ ⊔ ℓ') where
  constructor _,_ 
  field
    fst : B
    snd : E fst

infixr 50 _,_

syntax Σ B (λ x → E) = Σ[ x ∈ B ] E
```

Define the projection independently of the field names in the record:

```agda
-- projection to the base
π₁ : ∀ {ℓ ℓ'} {B : Set ℓ} {E : B → Set ℓ'} → Σ B E  → B
π₁ (b , e) = b

-- "projection" to the fiber
π₂ : ∀ {ℓ ℓ'} {B : Set ℓ} {E : B → Set ℓ'} (t : Σ B E) → E (π₁ t)
π₂ (b , e) = e
```

#### Induction and recursion principles {#indrec}

```agda
Σ-induction : ∀ {ℓ ℓ' ℓ''} {B : Set ℓ} {E : B → Set ℓ'} {P : Σ B E → Set ℓ''} →
              ( (b : B) → (e : E b) → P (b , e) ) → 
              (u : Σ B E) → P u
Σ-induction g (fst , snd) = g fst snd

-- Recursion from induction
Σ-recursion : ∀ {ℓ ℓ' ℓ''} {B : Set ℓ} {E : B → Set ℓ'} {P : Set ℓ''} →
              ( (b : B) → (e : E b) → P ) → Σ B E → P
Σ-recursion {P = P} = Σ-induction {P = (λ _ → P)}

-- Direct definition
Σ-recursion' : ∀ {ℓ ℓ' ℓ''} {B : Set ℓ} {E : B → Set ℓ'} {P : Set ℓ''} →
              ( (b : B) → (e : E b) → P ) → Σ B E → P
Σ-recursion' g (b , e) = g b e
```
The `Σ-induction` is also referred to as <span style="color: teal">uncurry</span>, after [Haskell Curry](https://en.wikipedia.org/wiki/Haskell_Curry). There is an inverse:

```agda
curry : ∀ {ℓ ℓ' ℓ''} {B : Set ℓ} {E : B → Set ℓ'} {P : Σ B E → Set ℓ''} →
        ( (u : Σ B E) → P u ) → 
        ( (b : B) → (e : E b) → P (b , e) )
curry f b e = f (b , e)
```
where a (dependent) function out of a Σ-type yields a two-variable function. (Note that the "uncurry" does exactly the opposite.)


<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---

### Cartesian Products {#cartesian}

```agda
-- non-dependent Σ-type = Cartesian product
_×_ : ∀{ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ') 
A × B = Σ A (λ x → B)
```

#### Induction and recursion principles {#indreccart}


```agda
×-induction : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {P : A × B → Set ℓ''} → 
               ((a : A) → (b : B) → P (a , b)) → (x : A × B) → P x
×-induction = Σ-induction

-- Direct definition
×-induction' : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {P : A × B → Set ℓ''} → 
               ((a : A) → (b : B) → P (a , b)) → (x : A × B) → P x
×-induction' g (a , b) = g a b
```

Since neither type is dependent, we can implement the standard swap of the factors in the Cartesian product:
```agda
×-swap : ∀ {ℓ ℓ'} {A : Set ℓ}{B : Set ℓ'} → A × B → B × A
×-swap (a , b) = b , a
```

```agda
-- FIXME: this is not used, remove it later
×-assoc : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} →
    (A × B) × C → A × (B × C)
×-assoc (( a , b ) , c) = a , (b , c)
```


