/-
Copyright (c) 2025 Leopold Mayer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dora Kassabova, Leopold Mayer, Haoming Ning
-/
module

public import Mathlib.RingTheory.RegularLocalRing.AuslanderBuchsbaumSerre
public import Mathlib.RingTheory.RegularLocalRing.GlobalDimension
public import Mathlib.RingTheory.UniqueFactorizationDomain.KaplanskyHeight1
public import Mathlib.RingTheory.PicardGroup

/-!
 guys we should change this
# Localization of Regular Local Ring is Regular

In this file, we establish the full version of Auslander-Buchsbaum-Serre criterion and its corollary
that localization of regular local ring is regular.

-/

@[expose] public section

universe u v

variable (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
variable (n : ℕ)

#check Ring.KrullDimLE.isField_of_isDomain
#check CommRing.Pic.subsingleton_iff

notation "m" => IsLocalRing.maximalIdeal

open Localization

#check (m R)^2
example (x : R) : CommRing (Localization.Away x) := inferInstance
/- how to express f/x^n in R_x -/
example (x f : R) (n : ℕ) : (Localization.Away x) := Localization.mk f ⟨x^n, ⟨n, rfl⟩⟩

#check WfDvdMonoid.exists_factors

theorem PicSubsingleton (x : R) : Subsingleton (CommRing.Pic (Localization.Away x)) := sorry

theorem invertibleIffLocalizations (M : Type) [AddCommGroup M] [Module R M]
  : Module.Invertible R M := sorry
set_option linter.style.longLine false


-- These two maybe should go into Noeth local ring sections if we keep it
/- A local ring with maximal ideal zero is of Krull dimension zero -/
lemma krull_dim_zero_of_maximal_ideal_zero {R : Type u}
    [CommRing R] [IsLocalRing R] (h : IsLocalRing.maximalIdeal R = ⊥)
    : ringKrullDim R = 0 := by
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h, Ideal.height_bot, WithBot.coe_zero]

/- In a Noetherian local ring of dim > 0,
there exists an element x in m \ m^2 -/
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
and p is prime then they are equal. q need not be prime -/
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

/- The span of a prime element in a Noetherian domain is height 1 -/
theorem height_one_of_prime_element {R : Type u}
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (p : R) (hp : Prime p) : (Ideal.span {p}).height = 1 := by
  -- First note that (p) is prime
  have hp_ne := Prime.ne_zero hp
  rw [← Ideal.span_singleton_prime hp_ne] at hp
  apply le_antisymm _ _
  -- The only minimal prime of (p) is itself
  · have h_minprime := (Ideal.span {p}).minimalPrimes_eq_subsingleton_self
    have h_minprime' : Ideal.span {p} ∈ (Ideal.span {p}).minimalPrimes := by aesop
    -- By Krull's Principal Ideal theorem, (p) has height at most 1
    exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
      (Ideal.span {p}) (Ideal.span {p}) h_minprime'
  -- Since R is a domain, non zero prime ideal have positive height
  · apply height_ge_one_of_prime_ne_bot hp
    simp [Ideal.span_singleton_eq_bot, hp_ne]

/- Nagata's criterion: If the image of an element is prime after localization, then it is prime -/
theorem prime_of_prime_in_localization {R : Type*} [CommRing R] [IsDomain R]
    (p : R) (hp_prime : Prime p) (x : R) (hx_irred : Irreducible x)
    (hax_prime : Prime (algebraMap R (Away p) x)) : Prime x := by
  -- First note that both x and its image are non-zero
  have hxp_ne := Prime.ne_zero hax_prime
  have hx_ne : x ≠ 0 := by
    intro hx
    apply hxp_ne
    simp only [hx, map_zero]
  refine ⟨ hx_ne, Irreducible.not_isUnit hx_irred, fun a b h => ?_ ⟩
  -- Suppose x | a * b, then in R_p a * b in (x)
  have habp : algebraMap R (Away p) (a * b) ∈ Ideal.span {algebraMap R (Away p) x} := by
    have hh : ⇑(algebraMap R (Away p)) '' {x} = {(algebraMap R (Away p)) x} := by aesop
    rw [← hh, ← Ideal.map_span (algebraMap R (Away p)) {x}]
    exact Ideal.mem_map_of_mem (algebraMap R (Away p)) (Ideal.mem_span_singleton.mpr h)
  rw [MulHomClass.map_mul] at habp
  -- Since (x) is prime, WLOG a in (x)
  rw [← Ideal.span_singleton_prime hxp_ne] at hax_prime
  rcases (hax_prime.mem_or_mem habp) with ha | hb
    -- So p^n * a = x * y for y in R
  · have hay : ∃ y : R, ∃ n : ℕ, a * p^n = x * y := by
      sorry -- **should be the same as Dora's first sorry**
    rcases hay with ⟨ y, n, hay ⟩
    by_cases hpx : (p ∣ x)
    -- If p divides x, x is prime since it is irreducible
    · have hxp_assoc := Irreducible.associated_of_dvd (Prime.irreducible hp_prime) hx_irred hpx
      have hx_prime := hxp_assoc.prime_iff.mp hp_prime
      exact hx_prime.2.2 a b h
    -- If p does not divide x, p^n divides y
    left
    have hdiv : p^n ∣ x * y := ⟨a, by simpa only [mul_comm] using hay.symm⟩
    have hpy := Prime.pow_dvd_of_dvd_mul_left (n := n) hp_prime hpx hdiv
    -- Then a is in (x), as desired
    rcases hpy with ⟨z, rfl⟩
    simp only [mul_comm, ← mul_assoc] at hay
    have hp_ne : p ^ n ≠ 0 := pow_ne_zero n (Prime.ne_zero hp_prime)
    have h := mul_right_cancel₀ hp_ne hay
    exact ⟨z, h⟩
  · -- same WLOG proof as above, but can't easily simplify into separate lemma because the by_cases and anti-symmetry
    have hby : ∃ y : R, ∃ n : ℕ, b * p^n = x * y := by
      sorry -- **should be the same as Dora's first sorry, and above**
    rcases hby with ⟨ y, n, hby ⟩
    by_cases hpx : (p ∣ x)
    · have hxp_assoc := Irreducible.associated_of_dvd (Prime.irreducible hp_prime) hx_irred hpx
      have hx_prime := hxp_assoc.prime_iff.mp hp_prime
      exact hx_prime.2.2 a b h
    right
    have hdiv : p^n ∣ x * y := ⟨b, by simpa only [mul_comm] using hby.symm⟩
    have hpy := Prime.pow_dvd_of_dvd_mul_left (n := n) hp_prime hpx hdiv
    rcases hpy with ⟨z, rfl⟩
    simp only [mul_comm, ← mul_assoc] at hby
    have hp_ne : p ^ n ≠ 0 := pow_ne_zero n (Prime.ne_zero hp_prime)
    have h := mul_right_cancel₀ hp_ne hby
    exact ⟨z, h⟩

/- Main theorem: regular local ring implies UFD -/
public theorem isUniqueFactorizationDomain' (n : ℕ) : ∀ R : Type u, [CommRing R] → [IsDomain R]
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
  rcases H1 with ⟨ x, hx ⟩
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
  /- If x is in p, then we are done -/
  by_cases hxp : x ∈ p
  · use x
    have hhxp := (Ideal.span_singleton_le_iff_mem p).mpr hxp
    have hxs_prime := (Ideal.span_singleton_prime (Prime.ne_zero hx_prime)).mpr hx_prime
    exact (eq_of_height_one_le_height_one_prime
      (Ideal.span {x}) p
      (height_one_of_prime_element x hx_prime)
      hp_height hhxp).symm
  /- Now that x is not in p, p_x is prime -/
  have hpx_prime : (p.map (algebraMap R (Away x))).IsPrime := sorry
  /- we see that p_x=(y) for some y ∈ R_x -/
  -- Is (p.map (algebraMap R (Away x))) the same as localization px??
  have hp_princ : ∃ y, (p.map (algebraMap R (Away x))) = Ideal.span {y} := sorry
  /- We can write y=x^ef for some f∈p and e∈Z. -/
  rcases hp_princ with ⟨y, hy⟩
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
  have ha_gen : Ideal.span {y} = Ideal.span {algebraMap R (Away x) a'} := by
    sorry
  have ha'_prime_image : Prime (algebraMap R (Away x) a') := by
    have ha'_ne : (algebraMap R (Away x) a') ≠ 0 := by sorry
    rw [← Ideal.span_singleton_prime ha'_ne, ← ha_gen, ← hy]
    exact hpx_prime
  /- As x is a prime element, we find that ai is prime in R -/
  have ha'_prime : Prime a' := prime_of_prime_in_localization
    x hx_prime a' (ha_irr a' ha'.left) ha'_prime_image
  /- Note also that <a'> has height 1 -/
  have ha'_height := height_one_of_prime_element a' ha'_prime
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
