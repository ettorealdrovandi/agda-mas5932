---
layout: page
title: "Martin-Löf Type Theory"
description: "A minimal Type Theory in Martin-Löf style"
chapter: 2
---

### Contents {#top}

1. [Universes](#universes)
1. [Finite Types](#finitetypes)
   1. [The Empty Type](#empty)
   1. [The One-Point Type](#onepoint)
   1. [Sum Types (Disjoint Union)](#sumtypes)
1. [Σ-Types](#sigma)
1. [Π-Types](#pi)
1. [Identity Types](#id)

--------------------------------------------------------

```agda
{-# OPTIONS --without-K --safe #-}

module mltt where
```

### Universes {#universes}

```agda
open import level renaming (zero to lzero; suc to lsuc) public
```
For the future, define one more level
```agda
1ℓ : Level
1ℓ = lsuc 0ℓ
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---

### Finite Types {#finitetypes}

#### The Empty Type {#empty}

```agda
open import mltt.empty public
```
<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>

#### The One-Point Type {#onepoint}

```agda
open import mltt.unit public
```
<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>


#### Sum Types (Disjoint Union) {#sumtypes}

```agda
open import mltt.sum public
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---

### Σ-Types {#sigma}

```agda
open import mltt.sigma public
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---

### Π-Types {#pi}

```agda
open import mltt.pi public
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---

### Identity Types {#id}

```agda
open import mltt.identity-types public
open import mltt.identity.path-composition public
open import mltt.identity.ap public
open import mltt.identity.transport public
```
<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---
