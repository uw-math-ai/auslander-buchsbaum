/-
Copyright (c) 2025 Leopold Mayer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dora Kassabova, Leopold Mayer, Haoming Ning
-/
module

public import Mathlib.RingTheory.RegularLocalRing.AuslanderBuchsbaumSerre
public import Mathlib.RingTheory.RegularLocalRing.GlobalDimension
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!

# Localization of Regular Local Ring is Regular

In this file, we establish the full version of Auslander-Buchsbaum-Serre criterion and its corollary
that localization of regular local ring is regular.

-/

@[expose] public section

universe u v

variable (R : Type u) [CommRing R] [IsDomain R]

instance isUniqueFactorizationDomain [IsRegularLocalRing R] : UniqueFactorizationMonoid R := by
  sorry
