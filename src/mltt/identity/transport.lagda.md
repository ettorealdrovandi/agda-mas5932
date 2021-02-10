---
title: "Identity types: transport"
subtitle: "Martin-Löf Type Theory"
description: "A minimal Type Theory in Martin-Löf style: Identity types. Transport lemmmas"
---

```agda
{-# OPTIONS --without-K --safe #-}

module mltt.identity.transport where

open import level renaming (zero to lzero; suc to lsuc)
open import function.core
open import mltt.identity-types
open import mltt.identity.path-composition
```

### Lemmas on transport

```agda
module transport-lemmas where

  private
    variable
      ℓ ℓ' : Level
      A : Set ℓ
      P : A → Set ℓ'

  -- transport is compatible with path composition
  transport◾ : {x y z : A} (p : x ≡ y) (q : y ≡ z) {u : P x} → 
               ( (transport P q) ∘′ (transport P p) ) u ≡ transport P (p ◾ q) u
  transport◾ refl q = refl

  -- transport is compatible with function composition
  transport∘ : ∀{ν} {X : Set ν} {x y : X} {f : X → A} 
               (p : x ≡ y) {u : P (f x)} → transport (P ∘′ f) p u ≡ transport P (ap f p) u
  transport∘ refl = refl

  -- transport is compatible with morphisms of fibrations (f : Π[ x ∈ A ] (P x → Q x))
  transport-cov : ∀ {ℓ''} {Q : A → Set ℓ''} {x y : A} {f : (x : A) → P x → Q x}
                   (p : x ≡ y) {u : P x} → transport Q p (f x u) ≡ f y (transport P p u)
  transport-cov {x = x} {f = f} refl {u} = idp (f x u)

  -- state transport-cov without the u : P x
  transport-cov' : ∀ {ℓ''} {Q : A → Set ℓ''} {x y : A} {f : (x : A) → P x → Q x}
                   (p : x ≡ y) → transport Q p ∘ (f x) ≡ (f y) ∘ (transport P p)
  transport-cov' refl = refl

  -- compatibility with identifications of path
  transport≡ : {x y : A} {p q : x ≡ y} (α : p ≡ q) {u : P x} →
              transport P p u ≡ transport P q u
  transport≡ refl = refl
```

The following lemmas are used to turn transport in path dependent types into path composition

```agda
module transport-in-paths where

  private
    variable
      ℓ : Level
      A : Set ℓ

  open ◾-lemmas

  transport-path-f : {a x y : A} (p : x ≡ y) (q : a ≡ x) →  
                     transport (λ v → a ≡ v) p q ≡ q ◾ p
  transport-path-f refl q = ru q ⁻¹

  transport-path-b : {a x y : A} (p : x ≡ y) (q : x ≡ a) →
                     transport (λ v → v ≡ a) p q ≡ p ⁻¹ ◾ q
  transport-path-b refl q = refl

  transport-path-id : {x y : A} (p : x ≡ y) (q : x ≡ x) →
                      transport (λ v → v ≡ v) p q ≡ (p ⁻¹ ◾ q) ◾ p
  transport-path-id refl q = ru q ⁻¹

  transport-path-id' : {x y : A} (p : x ≡ y) (q : x ≡ x) →
                       transport (λ v → v ≡ v) p q ≡ p ⁻¹ ◾ (q ◾ p)
  transport-path-id' refl q = ru q ⁻¹

  transport-path-parallel : ∀ {ℓ'} {B : Set ℓ'} {f g : A → B} {x y : A}
                            (p : x ≡ y) (q : f x ≡ g x) →
                            transport (λ v → f v ≡ g v) p q ≡ ((ap f p) ⁻¹ ◾ q) ◾ (ap g p)
  transport-path-parallel refl q = ru q ⁻¹

  transport-path-parallel' : ∀ {ℓ'} {B : Set ℓ'} {f g : A → B} {x y : A}
                             (p : x ≡ y) (q : f x ≡ g x) →
                             transport (λ v → f v ≡ g v) p q ≡ (ap f p) ⁻¹ ◾ (q ◾ ap g p)
  transport-path-parallel' refl q = ru q ⁻¹

  transport-path-fun-left : ∀ {ℓ'} {B : Set ℓ'} {f : A → B} {b : B} {x y : A}
                            (p : x ≡ y) (q : f x ≡ b) →
                            transport (λ v → f v ≡ b) p q ≡ (ap f p) ⁻¹ ◾ q
  transport-path-fun-left refl q = refl

  transport-path-fun-right : ∀ {ℓ'} {B : Set ℓ'} {b : B} {g : A → B} {x y : A}
                            (p : x ≡ y) (q : b ≡ g x) →
                            transport (λ v → b ≡ g v) p q ≡  q ◾ ap g p
  transport-path-fun-right refl q = ru q ⁻¹
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---
