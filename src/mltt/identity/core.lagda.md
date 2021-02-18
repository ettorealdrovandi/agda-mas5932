---
title: "Identity types"
subtitle: "Martin-Löf Type Theory, identity types"
description: "A minimal Type Theory in Martin-Löf style: Identity types"
---

### Contents {#top}

1. [Identity Types](#id)
1. [Path induction](#pathinduction)
   1. [Pauling-Mohring theorem](#paulin-mohring)
1. [Transport](#transport)
1. [Applicative](#ap)
1. [Inversion of identifications](#inversion)
1. [Composition of identifications](#composition)
1. [Reasoning with equality](#reasoning)

--------------------------------------------------------------------------------


```agda
{-# OPTIONS --without-K --safe #-}

module mltt.identity.core where

open import level
open import mltt.pi
open import function.core
```

### Identity Types {#id}

```agda
infix 4 _≡_  
data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
  instance refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

-- alternative HoTT name
Id : {ℓ : Level} (A : Set ℓ) → A → A → Set ℓ
Id {ℓ} A = _≡_ {ℓ} {A}

-- explicit version of refl
idp : {ℓ : Level} {A : Set ℓ} (x : A) → x ≡ x
idp x = refl {x = x}

-- recover implicit arguments in equalities
lhs : ∀{ℓ} {A : Set ℓ} {x y : A} → x ≡ y → A
lhs {ℓ} {A} {x} {y} p = x

rhs : ∀{ℓ} {A : Set ℓ} {x y : A} → x ≡ y → A
rhs {ℓ} {A} {x} {y} p = y
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---

### Path induction {#pathinduction}

```agda
≡-induction : ∀ {ℓ ℓ'} {A : Set ℓ} (D : (x y : A) → x ≡ y → Set ℓ') →
              ((x : A) → D x x refl) → ( (x y : A) → (p : x ≡ y) → D x y p )
≡-induction D d x .x refl = d x

𝕁 = ≡-induction
```

#### Paulin-Mohring theorem {#paulin-mohring}
```agda
ℍ : ∀ {ℓ ℓ'} {A : Set ℓ} (x : A) (C : (y : A) → x ≡ y → Set ℓ') → 
    C x refl → (y : A) → (p : x ≡ y) → C y p
ℍ x C c .x refl = c

𝕁' : ∀ {ℓ ℓ'} {A : Set ℓ} (D : (x y : A) → x ≡ y → Set ℓ') → 
     ((x : A) → D x x refl) → (x y : A) → (p : x ≡ y) → D x y p
𝕁' D d x y p = ℍ x (D x) (d x) y p

𝕁-to-𝕁' : ∀ {ℓ ℓ'} {A : Set ℓ} (D : (x y : A) → x ≡ y → Set ℓ')  
          (d : (x : A) → D x x refl) (x y : A) (p : x ≡ y) →
          𝕁 D d x y p ≡ 𝕁' D d x y p
𝕁-to-𝕁' D d x .x refl = idp (d x) -- signal which reflexivity with an explicit term

ℍ' : ∀ {ℓ ℓ'} {A : Set ℓ} (x : A) (C : (y : A) → x ≡ y → Set ℓ') → C x refl →
     (y : A) → (p : x ≡ y) → C y p
ℍ' {ℓ} {ℓ'} {A} x C c y p = 𝕁 𝔻 (λ x C c → c) x y p C c where 
  𝔻 : ∀ {ℓ ℓ'} {A : Set ℓ} → (x y : A) → (p : x ≡ y) → Set (ℓ ⊔ lsuc ℓ')
  𝔻 {ℓ} {ℓ'} {A} x y p = (C : ((y' : A) → (p' : x ≡ y') → Set ℓ')) → (C x refl → C y p)

--TODO: ℍ-to-ℍ'
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---

### Transport {#transport}

```agda
transport𝕁 : ∀{ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') {x y : A}
            (p : x ≡ y) → P x → P y
transport𝕁 {ℓ} {ℓ'} {A} P {x} {y} p = 𝕁 D d x y p 
  where
    D : ∀{ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} (x y : A) → x ≡ y → Set ℓ'
    D {P = P} x y p = P x → P y
    d : ∀{ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} (x : A) → D {P = P} x x refl
    d x = id

transport : ∀{ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') {x y : A}
            (p : x ≡ y) → P x → P y
transport P refl = id

transport-agreement : ∀ {ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') {x y : A} (p : x ≡ y) →
                      transport P p ≡ transport𝕁 P p
transport-agreement P refl = idp (id)
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---

### Applicative {#ap}

```agda
ap : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A} (f : A → B) → 
     x ≡ y → f x ≡ f y
ap f refl = refl

ap𝕁 : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A} (f : A → B) →
      x ≡ y → f x ≡ f y
ap𝕁 {ℓ} {ℓ'} {A} {B} {x} {y} f p = 𝕁 D d x y p where
  D : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} (x y : A) (p : x ≡ y) → Set ℓ'
  D {f = f} x y p = f x ≡ f y
  d : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} (x : A) → D {f = f} x x refl
  d x = refl

ap-agreement : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A} (f : A → B) (p : x ≡ y) → ap f p ≡ ap𝕁 f p
ap-agreement f refl = idp refl
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---

### Inversion of identifications {#inversion}

```agda
≡-inv𝕁 : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
≡-inv𝕁 {ℓ} {A} {x} {y} p = 𝕁 (λ x y p → y ≡ x) (λ x → refl) x y p

infixr 30 _⁻¹
_⁻¹ : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl

-- for symmetry
≡-inv = _⁻¹
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---

### Composition of identifications {#composition}

```agda
≡-comp𝕁 : ∀ {ℓ} {A : Set ℓ} {x y z : A} (p : x ≡ y ) → y ≡ z → x ≡ z
≡-comp𝕁 {ℓ} {A} {x} {y} {z} p = 𝕁 D d x y p z where 
    D : ∀ {ℓ} {A : Set ℓ} (x y : A) (p : x ≡ y) → Set ℓ
    D {ℓ} {A} x y p = (z : A) → (q : y ≡ z) → x ≡ z

    d : ∀ {ℓ} {A : Set ℓ} (x : A) → D x x refl -- Π[ z ∈ A ] Π[ q ∈ x ≡ z ] (x ≡ z)
    d {ℓ} {A} x z q = 𝕁 E (λ x → refl) x z q where
        E : ∀ {ℓ} {A : Set ℓ} → Π[ x ∈ A ] Π[ z ∈ A ] Π[ q ∈ x ≡ z ] Set ℓ
        E {ℓ} {A} x z q = x ≡ z

infix 25 _◾_
_◾_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
refl ◾ q = q

infix 25 _◾′_
_◾′_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
p ◾′ refl = p

◾-agreement : ∀ {ℓ} {A : Set ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → p ◾ q ≡ p ◾′ q
◾-agreement refl refl = refl
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---

### Reasoning with equality {#reasoning}

```agda
module ≡-Reasoning {ℓ : Level} {A : Set ℓ}  where

  infix 3 _∎
  infixr 2 _≡⟨_⟩_
  infix 1 begin_

  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin p = p
  
  _≡⟨_⟩_ : (x : A) {y z : A} →
           x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ p ⟩ q = p ◾ q

  _∎ : (x : A) → x ≡ x
  x ∎ = idp x
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---
