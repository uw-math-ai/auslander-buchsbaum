/-
Copyright (c) 2025 Leopold Mayer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dora Kassabova, Leopold Mayer, Haoming Ning
-/
module

public import Mathlib.RingTheory.RegularLocalRing.AuslanderBuchsbaumSerre
public import Mathlib.RingTheory.RegularLocalRing.GlobalDimension
-- public import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky
public import Mathlib.RingTheory.UniqueFactorizationDomain.KaplanskyHeight1

/-!

# Localization of Regular Local Ring is Regular

In this file, we establish the full version of Auslander-Buchsbaum-Serre criterion and its corollary
that localization of regular local ring is regular.

-/

@[expose] public section

universe u v

variable (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
variable (n : ℕ)

#check Ring.KrullDimLE.isField_of_isDomain

notation "m" => IsLocalRing.maximalIdeal

open Localization

#check (m R)^2
example (x : R) : CommRing (Localization.Away x) := inferInstance
/- how to express f/x^n in R_x -/
example (x f : R) (n : ℕ) : (Localization.Away x) := Localization.mk f ⟨x^n, ⟨n, rfl⟩⟩

#check WfDvdMonoid.exists_factors

-- These two maybe should go into Noeth local ring sections if we keep it
lemma krull_dim_zero_of_maximal_ideal_zero {R : Type u}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (h : IsLocalRing.maximalIdeal R = ⊥) : ringKrullDim R = 0 := by
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h, Ideal.height_bot, WithBot.coe_zero]

lemma exists_elem_in_maximal_not_in_maximal_sq (R : Type u)
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (h_dim : 0 < ringKrullDim R) : ∃ x ∈ m R, x ∉ (m R) ^ 2 := by
  -- Suppose for contradiction that m = m^2.
  by_contra h_contra
  have h_eq : IsLocalRing.maximalIdeal R = (IsLocalRing.maximalIdeal R)^2 := by
    apply le_antisymm _ _
    · aesop
    · exact Ideal.pow_le_self two_ne_zero
  -- By Nakayama's Lemma, since m is finitely generated, we have m = 0.
  have h_m_zero : IsLocalRing.maximalIdeal R = ⊥ := by
    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
    any_goals exact IsLocalRing.maximalIdeal R
    · exact IsNoetherian.noetherian _
    · simpa only [ sq ] using h_eq.le
    · exact IsLocalRing.maximalIdeal_le_jacobson ⊥
  -- If m = 0, then R is a zero-dimensional local ring.
  have h_krull_dim_zero : ringKrullDim R = 0 := by
    exact krull_dim_zero_of_maximal_ideal_zero h_m_zero
  exact h_dim.ne' h_krull_dim_zero

/- If two height one ideals $p, q$ has containment $p ≤ q$,
and p is primethen they are equal. q need not necessarily be prime -/
lemma eq_of_height_one_le_height_one_prime {R : Type u} [CommRing R]
    (p : Ideal R) (q : Ideal R) [hp : p.IsPrime]
    (hph : p.height = 1) (hqh : q.height = 1) (h : p ≤ q) : p = q := by
  -- Suppose for contradiction they are not equal
  by_contra hneq
  have hneq' : p ≠ q := by
    simpa [eq_comm] using hneq
  -- Then p is strictly contained in q
  have hlt : p < q := lt_of_le_of_ne h hneq'
  have hp_fin : p.FiniteHeight := by
    refine (Ideal.finiteHeight_iff p).mpr ?_
    right
    simpa only [hph] using ENat.one_ne_top
  -- Then p is of height < 1 because q is of height 1
  have hp_lt := Ideal.height_strict_mono_of_is_prime hlt
  rw [hph, hqh] at hp_lt
  contradiction

theorem isUniqueFactorizationDomain' (n : ℕ) : ∀ R : Type u, [CommRing R] → [IsDomain R]
    → [IsRegularLocalRing R] → (ringKrullDim R = n) → UniqueFactorizationMonoid R := by
  /- We will prove the unique factorization property by induction
    on the dimension of the regular local ring R -/
  induction n using Nat.strong_induction_on with
  | h n hn =>
  intros R _ _ _ hn
  cases n with
  /- If dim(R)=0, then R is a field and in particular a UFD -/
  | zero =>
  have HHH : Ring.KrullDimLE 0 R := by rw [Ring.krullDimLE_iff, hn]
  have H : IsField R := Ring.KrullDimLE.isField_of_isDomain
  have HH : IsPrincipalIdealRing R := IsField.isPrincipalIdealRing H
  apply PrincipalIdealRing.to_uniqueFactorizationMonoid
  /- Assume dim(R)>0 -/
  | succ n =>
  -- rw [Nat.cast_add, Nat.cast_one] at hn
  have Hdim: 0 < ringKrullDim R := by
    rw [hn]
    norm_cast
    exact Nat.zero_lt_succ n
  /- let x ∈ m \ m^2 -/
  have H1 : ∃ x, x ∈ (m R) ∧ x ∉ ((m R)^2) := by
    apply exists_elem_in_maximal_not_in_maximal_sq R Hdim
  cases H1 with
  | intro x hx =>
  /- then R/(x) is regular -/
  have Hx : IsRegularLocalRing (R ⧸ Ideal.span {x}) := by
    exact (quotient_span_singleton R hx.left hx.right).left
  /- hence a domain -/
  have Hx' : IsDomain (R ⧸ Ideal.span {x}) := isDomain_of_isRegularLocalRing _
  /- hence x is a prime element -/
  have hx_prime : Prime x := by
    rw[Ideal.Quotient.isDomain_iff_prime, Ideal.span_singleton_prime] at Hx'
    · exact Hx'
    intro hx_zero
    rcases hx with ⟨_, hx2⟩
    rw[hx_zero] at hx2
    · exact hx2 (Ideal.zero_mem ((m R)^2))
  rw [UniqueFactorizationMonoid.iff_height_one_prime_principal]
  intros p hp_prime hp_height
  /- we see that p_x=(y) for some y ∈ R_x -/
  have hp_princ : (p.map (algebraMap R (Away x))).IsPrincipal := sorry
  /- We can write y=x^ef for some f∈p and e∈Z. -/
  match hp_princ with
  | ⟨⟨y, hy⟩⟩ =>
  have hy : ∃ f : R, ∃ e : ℕ,
    f ∈ p ∧ y * (mk (x^e) ⟨1, one_mem _⟩) = (mk f ⟨1, one_mem _⟩) := by
    sorry
  /- Factor f=a1…ar into irreducible elements of R -/
  rcases hy with ⟨f, e, hfp, hf⟩
  rcases WfDvdMonoid.exists_factors f (sorry : f ≠ 0) with ⟨a, ha_irr, ha_prod⟩
  /- Since p is prime, we see that ai∈p for some i. -/
  have ha : ∃ a' ∈ a, a' ∈ p := sorry
  rcases ha with ⟨a', ha'⟩
  /-  Since p_x=(y) is prime and a_i | y in R_x, it follows that
  p_x is generated by a_i in R_x, i.e., the image of a_i in R_x is prime
  -/
  have ha_gen : Away x ∙ y = Away x ∙ (mk a' ⟨1, one_mem _⟩) := sorry
  have ha'_prime_image : Prime (algebraMap R (Away x) a') := sorry
  /- As x is a prime element, we find that ai is prime in R -/
  have ha'_prime : Prime a' := sorry
  /- Note also that <a'> has height 1 -/
  have ha'_height : (Ideal.span {a'}).height = 1 := by sorry
    -- something something easy direction of Krull's PIT
  use a'
  rw [eq_comm]
  rw [← Ideal.span_singleton_prime (Prime.ne_zero ha'_prime)] at ha'_prime
  /- Since <a'> <= p are both height 1 primes, we are done -/
  apply eq_of_height_one_le_height_one_prime (Ideal.span {a'}) p
  · exact ha'_height
  · exact hp_height
  · rw[Ideal.span_le]
    aesop


instance isUniqueFactorizationDomain [IsRegularLocalRing R] : UniqueFactorizationMonoid R := by
  obtain ⟨n, hn⟩ := exist_nat_eq R
  exact isUniqueFactorizationDomain' n R hn
