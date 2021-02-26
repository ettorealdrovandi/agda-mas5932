---
title: "Natural Numbers"
subtitle: "Standard and simple types in Martin-Löf Type Theory"
description: "Interface"
---

The operations defined in this section are denoted `+`, `*`, `^`. Use
`renaming` as necessary when importing this module.

```agda
{-# OPTIONS --without-K --safe #-}

module types.naturals where

open import types.naturals.core       public
open import types.naturals.properties public
open import types.naturals.order      public
open import types.naturals.decidable  public
```
