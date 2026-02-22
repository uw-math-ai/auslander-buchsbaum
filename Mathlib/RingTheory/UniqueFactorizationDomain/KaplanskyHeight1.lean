module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

-- public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
-- public import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
public import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherian R R]

/-
TODO: Possibly remove [IsNoetherian R R] by
removing the use of Ideal.finiteHeight_of_isNoetherianRing
-/

-- credit to monogenic extension team
lemma height_one_prime_principal_of_UFD {S : Type*} [CommRing S] [IsDomain S]
    [UniqueFactorizationMonoid S]
    (q : Ideal S) [hq_prime : q.IsPrime] (hq_height : q.height = 1) :
    ∃ q₀ : S, q = Ideal.span {q₀} := by
  -- Step 1: q ≠ ⊥ because height q = 1 > 0
  have hq_ne_bot : q ≠ ⊥ := by
    intro h
    rw [h, Ideal.height_bot] at hq_height
    exact zero_ne_one hq_height
  -- Step 2: By UFD property, every nonzero prime ideal contains a prime element
  obtain ⟨p, hp_mem, hp_prime⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot hq_prime hq_ne_bot
  -- Step 3: span {p} is a prime ideal since p is prime
  have h_span_prime : (Ideal.span {p}).IsPrime := by
    rw [Ideal.span_singleton_prime hp_prime.ne_zero]
    exact hp_prime
  -- Step 4: span {p} ⊆ q
  have h_span_le : Ideal.span {p} ≤ q := (Ideal.span_singleton_le_iff_mem (I := q)).mpr hp_mem
  -- Step 5: span {p} ≠ ⊥
  have h_span_ne_bot : Ideal.span {p} ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact hp_prime.ne_zero
  -- Step 6: Since height q = 1, if span {p} < q, then span {p} has height 0
  -- In a domain, height 0 primes are just ⊥, but span {p} ≠ ⊥, contradiction.
  -- So span {p} = q.
  have h_eq : Ideal.span {p} = q := by
    by_contra h_ne
    have h_lt : Ideal.span {p} < q := lt_of_le_of_ne h_span_le h_ne
    -- height (span {p}) < height q = 1, so height (span {p}) = 0
    haveI : (Ideal.span {p}).IsPrime := h_span_prime
    have hq_ht_ne_top : q.height ≠ ⊤ := by
      rw [hq_height]
      exact ENat.one_ne_top
    haveI : q.FiniteHeight := ⟨Or.inr hq_ht_ne_top⟩
    haveI : (Ideal.span {p}).FiniteHeight := Ideal.finiteHeight_of_le h_span_le hq_prime.ne_top
    have h_ht_lt := Ideal.height_strict_mono_of_is_prime h_lt
    rw [hq_height] at h_ht_lt
    -- height (span {p}) < 1 means height (span {p}) = 0
    have h_ht_zero : (Ideal.span {p}).height = 0 := ENat.lt_one_iff_eq_zero.mp h_ht_lt
    -- span {p} is a minimal prime of S (height 0 prime)
    rw [Ideal.height_eq_primeHeight, Ideal.primeHeight_eq_zero_iff] at h_ht_zero
    -- In a domain, minimalPrimes of (⊥ : Ideal S) is just {⊥}
    have h_span_eq_bot : Ideal.span {p} = ⊥ := by
      have h_mem : Ideal.span {p} ∈ (⊥ : Ideal S).minimalPrimes := h_ht_zero
      -- (⊥ : Ideal S).minimalPrimes = minimalPrimes S by definition
      have : (⊥ : Ideal S).minimalPrimes = minimalPrimes S := rfl
      rw [this, IsDomain.minimalPrimes_eq_singleton_bot] at h_mem
      exact Set.mem_singleton_iff.mp h_mem
    exact h_span_ne_bot h_span_eq_bot
  exact ⟨p, h_eq.symm⟩


-- credit to Brian Nugent for simple proof with two lemmas
-- For $P$ prime ideal of finite positive height, there exists a prime ideal $Q≤ P$ with height one
lemma exists_height_one_le_of_finite_height {R : Type*} [CommRing R] [IsDomain R]
    {P : Ideal R} (h_prime : P.IsPrime) (h_fin : P.FiniteHeight) (hP : P.primeHeight ≥ 1) :
    ∃ Q ≤ P, Q.IsPrime ∧ Q.height = 1 := by
  -- If height P is one, then done
  by_cases hP : P.primeHeight = 1
  · rw[← P.height_eq_primeHeight] at hP
    use P
  -- Otherwise, height P > 1
  have hPgt1 : 1 < P.primeHeight := by
    rw[lt_iff_le_and_ne]
    refine ⟨?_, by push_neg at hP; exact hP.symm⟩
    expose_names; exact le_of_eq_of_le rfl hP_1
  -- We obtain an element of height 1 preceeding P in PrimeSpectrum R
  obtain ⟨Q, hQ⟩ := (Order.coe_lt_height_iff P.primeHeight_lt_top).mp hPgt1
  use Q.asIdeal
  exact ⟨hQ.1.1, ⟨ Q.2, by rw[Ideal.height_eq_primeHeight]; exact hQ.right ⟩⟩

-- Height of non zero prime ideal in a domain is greater than or equal to one
public lemma height_ge_one_of_prime_ne_bot {R : Type*} [CommRing R] [IsDomain R]
    {P : Ideal R} (h_prime : P.IsPrime) (h_ne : P ≠ ⊥) :
    P.height ≥ 1 := by
  -- Suppose P is height 0
  by_contra hC
  push_neg at hC
  rw[ENat.lt_one_iff_eq_zero, P.height_eq_primeHeight] at hC
  -- Order.height is defined for P : PrimeSpectrum R
  let Pp : PrimeSpectrum R := ⟨ P, h_prime ⟩
  change Order.height Pp = 0 at hC
  -- Then P is the zero ideal since R is domain
  rw[Order.height_eq_zero, isMin_iff_eq_bot] at hC
  have : Pp.asIdeal = ⊥ := by
    rw[hC]
    simp only [PrimeSpectrum.asIdeal_bot]
  exact h_ne this

namespace UniqueFactorizationMonoid

-- Height one prime is principal implies UFD
public theorem of_height_one_prime_principal : (∀ (I : Ideal R), I.IsPrime →
    I.height = 1 → ∃ x : R, I = Ideal.span {x}) → UniqueFactorizationMonoid R := by
  intro h
  rw[iff_exists_prime_mem_of_isPrime]
  intros I hI_ne hI_prime
  -- Since R is a domain, height of I is >= 1
  have hIge1 : I.height ≥ 1 := height_ge_one_of_prime_ne_bot hI_prime hI_ne
  -- There exists a height 1 prime ideal I contained in J
  have hJ : ∃ (J : Ideal R), J ≤ I ∧ J.IsPrime ∧ J.height = 1 := by
    apply exists_height_one_le_of_finite_height
    · exact Ideal.finiteHeight_of_isNoetherianRing I
    · rw[I.height_eq_primeHeight] at hIge1
      exact hIge1
  rcases hJ with ⟨J, hJI, hJprime, h_height⟩
  -- By hypothesis J is principal
  have hJ_princ := h J hJprime h_height
  obtain ⟨x, hx⟩ := hJ_princ
  -- Since J is height 1, it is not the zero ideal
  have hJ_ne: J ≠ ⊥ := by
    intro h_bot
    rw [h_bot, Ideal.height_bot (R := R)] at h_height
    cases h_height
  -- Then x is not zero
  have hx_ne : x ≠ 0 := by
    intro hx_zero
    apply hJ_ne
    rw [hx, hx_zero]
    exact Ideal.span_singleton_zero
  -- Then x is prime
  have hx_prime : Prime x := by
    rw [hx] at hJprime
    exact (Ideal.span_singleton_prime hx_ne).mp hJprime
  -- Also x is in J
  have hxJ : x ∈ J := by
    rw [hx]
    have hx_set : x ∈ ({x} : Set R) := by aesop
    exact Ideal.subset_span hx_set
  -- Then x is in I
  exact ⟨x, hJI hxJ, hx_prime⟩

-- UFD if and only if every height one prime is principal
public theorem iff_height_one_prime_principal :
    UniqueFactorizationMonoid R ↔ (∀ (I : Ideal R), I.IsPrime →
    I.height = 1 → ∃ x : R, I = Ideal.span {x}):= by
  constructor
  · intros hR_UFD I hI_prime hI_height
    exact height_one_prime_principal_of_UFD I hI_height
  · exact of_height_one_prime_principal

end UniqueFactorizationMonoid
