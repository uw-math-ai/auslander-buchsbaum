import Mathlib


--In this file we prove Nagata's criterion for UFD: if R is a Noetherian domain
--and T is the localization of R at a prime element f, and T is a UFD,
--then R is also a UFD.
--The main theorem is nagata_theorem at the bottom of the file.

--The proof folllows the outline in https://www.math.wustl.edu/~kumar/courses/Algebra5031fall2015/Nagata.pdf

--show that the algebra map from R to its localization T is injective
theorem nagata_setup {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] [IsDomain R]
    [IsDomain T] (f : R) (hf0 : f ≠ 0) (hT : IsLocalization.Away (f : R) T) :
    Function.Injective (algebraMap R T) :=
  IsLocalization.injective T (powers_le_nonZeroDivisors_of_noZeroDivisors hf0)

--factorization in the UFD T
theorem factors_in_T {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] [IsDomain R]
    [IsDomain T] (f : R) (hf0 : f ≠ 0) (hT : IsLocalization.Away (f : R) T)
    [UniqueFactorizationMonoid T] (x : R) (hx : x ≠ 0) :
    ∃ s : Multiset T, (∀ p ∈ s, Prime p) ∧ Associated (s.prod : T) (algebraMap R T x) := by
  have inj := nagata_setup f hf0 hT
  have h_img_ne : algebraMap R T x ≠ 0 := by
    intro h
    have : x = 0 := inj (by simp [h])
    contradiction
  exact UniqueFactorizationMonoid.exists_prime_factors (algebraMap R T x) h_img_ne

--lemma to lift elements from T to R up to association
theorem clears_denominators {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] [IsDomain R]
  [IsDomain T] (f : R) (hT : IsLocalization.Away (f : R) T) (z : T) :
    ∃ a : R, Associated z (algebraMap R T a) := by
  -- `IsLocalization.Away.sec` chooses `a : R` and `n : ℕ` such that
  -- `z * algebraMap R T (f ^ n) = algebraMap R T a`. Mathlib proves the sharper
  -- `Associated (algebraMap R T a) z` in `associated_sec_fst`, so we can use that.
  let a := (IsLocalization.Away.sec f z).1
  exact ⟨a, (IsLocalization.Away.associated_sec_fst (x := f) z).symm⟩

/-
If `q : T` is a prime element of the localization `T`, this lemma states that `q` comes from
some prime `p : R` up to a unit in `T` — i.e. `q` is associated to `algebraMap R T p`.
-/
theorem prime_in_T_lifts_to_R {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] [IsDomain R]
  [IsDomain T] [IsNoetherianRing R] (f : R) (hf0 : f ≠ 0) (hfprime : Prime f)
  (hT : IsLocalization.Away (f : R) T) (q : T) (hq : Prime q) :
  ∃ p : R, Prime p ∧ Associated q (algebraMap R T p) ∧ ¬ (f ∣ p) := by
  -- pick some representative `a0 : R` of `q` from the localization
  let a0 := (IsLocalization.Away.sec f q).1
  have h_assoc0 : Associated q (algebraMap R T a0) :=
    (IsLocalization.Away.associated_sec_fst (x := f) q).symm

  -- `a0` is nonzero (its image is associated to the nonzero prime `q`).
  have ha0 : a0 ≠ 0 := by
    intro ha0
    have : algebraMap R T a0 = 0 := by simp [ha0]
    have : q = 0 := by
      obtain ⟨u, hu⟩ := h_assoc0
      calc
        q = q * (u * u⁻¹) := by simp
        _ = (q * u) * u⁻¹ := by ring
        _ = algebraMap R T a0 * u⁻¹ := by rw [← hu]
        _ = 0 * u⁻¹ := by rw [this]
        _ = 0 := by simp
    exact hq.ne_zero this

  -- from Noetherianity we get the well-founded divisibility property
  have wf : WfDvdMonoid R := IsNoetherianRing.wfDvdMonoid

  -- remove all factors of `f` from `a0` using the maximal-power lemma
  obtain ⟨n, a, a_ndvd, ha0_eq⟩ := WfDvdMonoid.max_power_factor ha0 hfprime.irreducible
  -- now `a0 = f ^ n * a` and `¬ f ∣ a`.

  -- the image of `f` is a unit in the localization; make this available
  have unit_f_global := hT.algebraMap_isUnit (x := f)

  -- algebraMap a0 = (algebraMap f) ^ n * algebraMap a, so algebraMap a is associated to a0
  have map_eq : algebraMap R T a0 = (algebraMap R T f) ^ n * algebraMap R T a := by
    simp [ha0_eq, map_mul, map_pow]
  have unit_pow : IsUnit ((algebraMap R T f) ^ n) := IsUnit.pow n unit_f_global
  have assoc_eq : Associated (algebraMap R T a0) ((algebraMap R T f) ^ n * algebraMap R T a) :=
    Associated.of_eq map_eq
  have assoc_mul := associated_unit_mul_left (algebraMap R T a) ((algebraMap R T f) ^ n) unit_pow
  have h_assoc : Associated q (algebraMap R T a) :=
    (h_assoc0.trans assoc_eq).trans assoc_mul

  -- since `algebraMap R T a` is associated to `q`, it is prime in `T`.
  have prime_map_a : Prime (algebraMap R T a) := Associated.prime h_assoc hq

  -- now `a` is the reduced representative with `¬ f ∣ a`
  have f_ndivide_a : ¬ (f ∣ a) := a_ndvd

-- finally, show that `a` is prime in `R` using the definition of primality
  have h_prime_a : Prime a := by
    constructor
    · -- a ≠ 0: since its image is associated to the nonzero prime q
      intro ha_zero
      have : algebraMap R T a = 0 := by simp [ha_zero]
      have : q = 0 := by
        obtain ⟨u, hu⟩ := h_assoc
        calc q = q * (u * u⁻¹) := by simp
          _ = (q * u) * u⁻¹ := by ring
          _ = algebraMap R T a * u⁻¹ := by rw [← hu]
          _ = 0 * u⁻¹ := by rw [this]
          _ = 0 := by simp
      exact hq.ne_zero this
    · constructor
      · -- a is not a unit: otherwise algebraMap a would be a unit,
        -- so q (associated) would be a unit, contradicting `hq`.
        intro ha_unit
        have : IsUnit (algebraMap R T a) := IsUnit.map (algebraMap R T) ha_unit
        -- associated elements share unit-ness: use `Associated.isUnit` on `h_assoc.symm`
        have : IsUnit q := Associated.isUnit h_assoc.symm this
        exact hq.not_unit this
      · -- primality: if a ∣ b * c in R then a ∣ b or a ∣ c
        intros b c hab
        obtain ⟨d, hd⟩ := hab
        have : algebraMap R T a ∣ (algebraMap R T b * algebraMap R T c) := by
          use algebraMap R T d
          calc
            algebraMap R T b * algebraMap R T c = algebraMap R T (b * c) := by simp [map_mul]
            _ = algebraMap R T (a * d) := by rw [hd]
            _ = algebraMap R T a * algebraMap R T d := by simp [map_mul]
        let div_case := Prime.dvd_or_dvd prime_map_a this

        -- helper: clear denominators and peel off powers of `f` for a single factor `x`.
        have inj := nagata_setup f hf0 hT
        have case_for : ∀ x : R, (algebraMap R T a ∣ algebraMap R T x) → a ∣ x := by
          intro x hx
          obtain ⟨e, he⟩ := hx
          obtain ⟨n, r, hs'⟩ := IsLocalization.Away.surj f e
          have eq_xf_ar : algebraMap R T (x * f ^ n) = algebraMap R T (a * r) := by
            calc
              algebraMap R T (x * f ^ n) = algebraMap R T x * (algebraMap R T f) ^ n := by
                simp [map_mul]
              _ = (algebraMap R T a * e) * (algebraMap R T f) ^ n := by
                rw [he]
              _ = algebraMap R T a * (e * (algebraMap R T f) ^ n) := by
                ring
              _ = algebraMap R T a * algebraMap R T r := by
                rw [hs']
              _ = algebraMap R T (a * r) := by
                simp [map_mul]
          have eq_in_R : x * f ^ n = a * r := inj (by simp [eq_xf_ar])
          have key : ∀ (n : Nat) (r : R), x * f ^ n = a * r → a ∣ x := by
            intro n r h
            induction n generalizing r with
            | zero => use r; simpa [pow_zero] using h
            | succ n ih =>
              have f_dvd_ar : f ∣ a * r := by
                use x * f ^ n
                calc
                  a * r = x * f ^ (n + 1) := by rw [h]
                  _ = f * (x * f ^ n) := by ring
              have hcases := (hfprime.dvd_mul).1 f_dvd_ar
              cases hcases with
              | inl hf_a => exact (f_ndivide_a hf_a).elim
              | inr hf_r =>
                obtain ⟨r', hr⟩ := hf_r
                have h' : x * f ^ (n + 1) = a * (f * r') := by rw [hr] at h; exact h
                have mul_expr : ((x * f ^ n) - (a * r')) * f =
                    x * f ^ (n + 1) - a * (f * r') := by
                  ring
                have : ((x * f ^ n) - (a * r')) * f = 0 := by rw [mul_expr, h']; simp
                have left_zero := (mul_eq_zero.mp this).resolve_right hf0
                have eq' : x * f ^ n = a * r' := sub_eq_zero.1 left_zero
                exact ih r' eq'
          exact key n r eq_in_R

        -- now finish the two cases: a ∣ b or a ∣ c
        cases div_case with
        | inl hdiv => exact Or.inl (case_for b hdiv)
        | inr hdiv => exact Or.inr (case_for c hdiv)


  exact ⟨a, h_prime_a, h_assoc, f_ndivide_a⟩

--use above lemma to lift a multiset of primes in T to R
theorem lift_multiset_of_primes {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [IsDomain R] [IsDomain T] [IsNoetherianRing R]
    (f : R) (hf0 : f ≠ 0) (hfprime : Prime f) (hT : IsLocalization.Away (f : R) T)
    [UniqueFactorizationMonoid T] :
    ∀ s : Multiset T, (∀ p ∈ s, Prime p) → ∃ sR : Multiset R,
      (∀ p ∈ sR, Prime p) ∧ (∀ p ∈ sR, ¬ (f ∣ p)) ∧
      Associated (s.prod : T) (algebraMap R T (sR.prod)) := by
  intro s hs_primes
  induction s using Multiset.induction with
  | empty =>
    use (0 : Multiset R)
    constructor
    · intro p hp; cases hp
    constructor
    · intro p hp; cases hp
    · exact Associated.of_eq (by simp [Multiset.prod_zero])
  | cons p s ih =>
    have hp : Prime p := hs_primes p (Multiset.mem_cons_self p s)
    obtain ⟨r, hr_prime, h_assoc_p, hr_ndvd⟩ := prime_in_T_lifts_to_R f hf0 hfprime hT p hp
    have ih_arg := fun q hq => hs_primes q (Multiset.mem_cons_of_mem hq)
    obtain ⟨sR', hsR'_primes, hsR'_ndiv, hs_assoc'⟩ := ih ih_arg
    obtain ⟨u1, hu1⟩ := hs_assoc'
    obtain ⟨u2, hu2⟩ := h_assoc_p
    have mul_eq : (p ::ₘ s).prod * (u2 * u1) = algebraMap R T ((sR' + {r}).prod) := by
      calc
        (p ::ₘ s).prod * (u2 * u1) = p * s.prod * (u2 * u1) := by simp [Multiset.prod_cons]
        _ = p * (s.prod * (u2 * u1)) := by ring
        _ = p * (s.prod * u1 * u2) := by ring
        _ = p * (algebraMap R T (sR'.prod) * u2) := by rw [← hu1]
        _ = (p * u2) * algebraMap R T (sR'.prod) := by ring
        _ = (algebraMap R T r) * algebraMap R T (sR'.prod) := by rw [hu2]
        _ = algebraMap R T (r * sR'.prod) := by simp [map_mul]
        _ = algebraMap R T ((sR' + {r}).prod) := by simp [Multiset.prod_add, mul_comm, map_mul]
    use sR' + {r}
    apply And.intro
    · intro q hq; cases Multiset.mem_add.1 hq with
      | inl h => exact hsR'_primes q h
      | inr h => have : q = r := Multiset.mem_singleton.1 h; subst this; exact hr_prime
    apply And.intro
    · intro q hq; cases Multiset.mem_add.1 hq with
      | inl h => exact hsR'_ndiv q h
      | inr h => have : q = r := Multiset.mem_singleton.1 h; subst this; exact hr_ndvd
    · use (u2 * u1); exact mul_eq

--main existence lemma for Nagata's Criterion,
--lifting factorizations from T to R modulo some powers of f, but f is a prime element in R
--So it completes to a full factorization in R by adding some copies of f to the multiset.
theorem existence_step {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] [IsDomain R]
    [IsDomain T] [IsNoetherianRing R] (f : R) (hf0 : f ≠ 0) (hfprime : Prime f)
    (hT : IsLocalization.Away (f : R) T) [UniqueFactorizationMonoid T] :
    ∀ x : R, x ≠ 0 → ∃ sR : Multiset R, (∀ p ∈ sR, Prime p) ∧ Associated (sR.prod : R) x := by

  --factor algebraMap x in T, then lift the factors to R up to association by the previous lemmas
  intro x hx
  obtain ⟨s, hs_primes, hs_assoc⟩ := factors_in_T f hf0 hT x hx
  obtain ⟨sR, hsR_primes, hsR_ndiv, hsR_assoc_T⟩ :=
    lift_multiset_of_primes f hf0 hfprime hT s hs_primes
  have final_assoc := (hsR_assoc_T).symm.trans hs_assoc
  obtain ⟨u, hu⟩ := final_assoc
  obtain ⟨n, a', ha'⟩ := IsLocalization.Away.surj f (u : T)
  have prod_eq : algebraMap R T (sR.prod * a') = algebraMap R T (x * f ^ n) := by
    calc
      algebraMap R T (sR.prod * a') =
          algebraMap R T (sR.prod) * algebraMap R T a' := by
        simp [map_mul]
      _ = algebraMap R T (sR.prod) * (u * (algebraMap R T f) ^ n) := by
        rw [← ha']
      _ = (algebraMap R T (sR.prod) * u) * (algebraMap R T f) ^ n := by ring
      _ = algebraMap R T x * (algebraMap R T f) ^ n := by
        rw [hu]
      _ = algebraMap R T (x * f ^ n) := by simp [map_mul]
  have inj := nagata_setup f hf0 hT
  have eq_in_R : sR.prod * a' = x * f ^ n := inj (by simp [prod_eq])

  -- Since f is prime and does not divide any prime factor of sR, it does not divide sR.prod.
  have f_ndvd_prod : ¬ (f ∣ sR.prod) := by
    have h_list : ¬ (f ∣ (sR.toList).prod) := by
      apply Prime.not_dvd_prod hfprime
      intro a ha
      have : a ∈ sR := by simpa [Multiset.mem_toList] using ha
      exact hsR_ndiv a this
    have prod_eq_list := (Multiset.prod_toList sR).symm
    intro h
    have h' : f ∣ (sR.toList).prod := by rwa [prod_eq_list] at h
    exact h_list h'

  -- Split on whether the exponent `n` is positive or zero. We handle the `n > 0`
  -- Note: we will only prove `f ∣ a'` in the branch where `n > 0`.
  -- `n > 0` case first because it will be reduced to the `n = 0` case by dividing `a'` by `f`.
  have h_exists : ∃ a'' : R, Associated (sR.prod * a'') x := by
    -- define a recursive predicate: for any `m` and `a` with `sR.prod * a = x * f ^ m`
    -- produce the required `a''` by cancelling powers of `f` one-by-one.
    have rec_aux : ∀ m a, sR.prod * a = x * f ^ m → ∃ a'', Associated (sR.prod * a'') x := by
      intro m a heq
      induction m generalizing a with
      | zero =>
        use a
        simp [pow_zero] at heq
        exact Associated.of_eq heq
      | succ m' ih =>
        -- f divides the right-hand side, so f divides `sR.prod * a` with witness `x * f ^ m'`.
        have h_dvd : f ∣ (sR.prod * a) := by
          rw [heq]
          use x * f ^ m'
          ring
        cases (hfprime.dvd_mul).1 h_dvd with
        | inl hf_sR => exact (f_ndvd_prod hf_sR).elim
        | inr hf_a =>
          obtain ⟨a1, ha1⟩ := hf_a
          -- substitute `a = f * a1` and cancel one `f` from both sides
          have heq1 : sR.prod * (f * a1) = x * f ^ (m' + 1) := by
            rw [ha1] at heq
            exact heq
          have eq_mul : (sR.prod * a1) * f = (x * f ^ m') * f := by
            calc
              (sR.prod * a1) * f = sR.prod * (a1 * f) := by ring
              _ = sR.prod * (f * a1) := by ring
              _ = x * f ^ (m' + 1) := by exact heq1
              _ = (x * f ^ m') * f := by simp [pow_succ, mul_assoc]
          have eq_reduced : sR.prod * a1 = x * f ^ m' := mul_right_cancel₀ hf0 eq_mul
          exact ih a1 eq_reduced
    exact rec_aux n a' eq_in_R

  -- now we have some `a''` with `sR.prod * a''` associated to `x`
  obtain ⟨a'', h_assoc⟩ := h_exists
  have h_map_unit : IsUnit (algebraMap R T a'') := by
    -- h_assoc : (sR.prod * a'') * v = x for some unit v in R
    obtain ⟨v, hv⟩ := h_assoc
    -- map that equality to T and massage into a convenient shape
    have map_hv_raw := congrArg (algebraMap R T) hv
    have map_hv : (algebraMap R T (sR.prod * a'')) * (algebraMap R T (↑v)) = algebraMap R T x := by
      simpa [map_mul] using map_hv_raw
    have map_eq_raw :
      (algebraMap R T (sR.prod) * (algebraMap R T a'') * (algebraMap R T (↑v)))
      = algebraMap R T (sR.prod) * (u : T) := by
      calc
        (algebraMap R T (sR.prod) * (algebraMap R T a'') * (algebraMap R T (↑v)))
          = (algebraMap R T (sR.prod * a'')) * (algebraMap R T (↑v)) := by simp [map_mul]
        _ = algebraMap R T x := by exact map_hv
        _ = algebraMap R T (sR.prod) * (u : T) := by rw [hu]
    have map_eq := by simpa using map_eq_raw
    -- `algebraMap R T (sR.prod)` is nonzero.
    -- Its product with the unit `u` equals `algebraMap R T x`, so `x` would be 0 otherwise.
    have map_sR_ne : algebraMap R T (sR.prod) ≠ 0 := by
      intro H
      have map_x_zero : algebraMap R T x = 0 := by rw [← hu]; simp [H]
      have inj := nagata_setup f hf0 hT
      have : x = 0 := inj (by simp [map_x_zero])
      contradiction
    -- cancel the common left factor `algebraMap R T (sR.prod)` in the domain `T`
    have map_eq2 :
      (algebraMap R T sR.prod) * ((algebraMap R T a'') * (algebraMap R T (↑v)))
      = (algebraMap R T sR.prod) * (u : T) := by
      simpa [mul_assoc] using map_eq
    have mul_cancel := mul_left_cancel₀ map_sR_ne map_eq2
    -- now (algebraMap a'') * (algebraMap v) = ↑u, so algebraMap a'' is a unit
    let unit_v := Units.map (algebraMap R T : R →* T) v
    -- we have (algebraMap a'') * ↑unit_v = ↑u by `mul_cancel`
    have hprod_unit : (algebraMap R T a'') * (↑unit_v * ↑(u⁻¹)) = 1 := by
      have h1 : (algebraMap R T a'') * ↑unit_v = (u : T) := mul_cancel
      calc
        (algebraMap R T a'') * (↑unit_v * ↑(u⁻¹)) =
            ((algebraMap R T a'') * ↑unit_v) * ↑(u⁻¹) := by ring
        _ = ↑u * ↑(u⁻¹) := by rw [h1]
        _ = 1 := by simp
    let unit_w := Units.mkOfMulEqOne (algebraMap R T a'') (↑unit_v * ↑(u⁻¹)) hprod_unit
    have : (unit_w : T) = algebraMap R T a'' := Units.val_mkOfMulEqOne hprod_unit
    use unit_w

  -- we have shown the image of `a''` in `T` is a unit
  have h_a_map_unit := h_map_unit

  -- since `algebraMap R T a''` is a unit in `T`, obtain an inverse `e : T`.
  obtain ⟨e, he_right⟩ := IsUnit.exists_right_inv h_a_map_unit
  -- because `T` is commutative, the right-inverse is also a left-inverse.
  have he_left : e * algebraMap R T a'' = 1 := by
    rw [mul_comm]
    exact he_right

  -- now we can lift e, find e' in R such that e' = e * f^m for some m
  obtain ⟨m, e', he'⟩ := IsLocalization.Away.surj f e
  -- calculate the product a'' * e' in R
  have prod_eq_in_R : a'' * e' = f ^ m := by
    have map_eq : algebraMap R T (a'' * e') = algebraMap R T (f ^ m) := by
      calc
        algebraMap R T (a'' * e') = (algebraMap R T a'') * (algebraMap R T e') := by simp [map_mul]
        _ = (algebraMap R T a'') * (e * (algebraMap R T f) ^ m) := by rw [he']
        _ = (algebraMap R T a'' * e) * (algebraMap R T f) ^ m := by ring
        _ = 1 * (algebraMap R T f) ^ m := by rw [he_right]
        _ = algebraMap R T (f ^ m) := by simp [map_pow]

    have inj := nagata_setup f hf0 hT
    exact inj map_eq

  -- use the prime-power splitting lemma to conclude `a''` is a power of `f` times a unit
  have hx : a'' * e' = (1 : R) * f ^ m := by
    calc
      a'' * e' = f ^ m := prod_eq_in_R
      _ = (1 : R) * f ^ m := by simp
  rcases mul_eq_mul_prime_pow hfprime hx with ⟨i, j, b, c, hij, hb_mul_c, ha''_eq, he'_eq⟩
  -- here `1 = b * c`, `a'' = b * f ^ i`, `e' = c * f ^ j` and `i + j = m`.
  have hb_unit : IsUnit b := isUnit_of_mul_eq_one b c (Eq.symm hb_mul_c)

  -- form the final multiset by adding `i` copies of `f` to `sR`.
  let sR_fin := sR + Multiset.replicate i f
  have prod_rep : sR_fin.prod = sR.prod * (f ^ i) := by simp [sR_fin]
  have eq_prod_b : sR_fin.prod * b = sR.prod * a'' := by
    calc
      sR_fin.prod * b = (sR.prod * f ^ i) * b := by simp [prod_rep]
      _ = sR.prod * (f ^ i * b) := by ring
      _ = sR.prod * a'' := by rw [mul_comm (f ^ i) b, ha''_eq.symm]
  have assoc_step1 : Associated sR_fin.prod (sR_fin.prod * b) := by
    have one_assoc_rev : Associated b (1 : R) := associated_one_iff_isUnit.mpr hb_unit
    let one_assoc := one_assoc_rev.symm
    have h := Associated.mul_left sR_fin.prod one_assoc
    simpa [mul_one] using h
  have assoc_step2 : Associated (sR_fin.prod * b) (sR.prod * a'') := Associated.of_eq eq_prod_b
  have final_associated : Associated sR_fin.prod x :=
    assoc_step1.trans (assoc_step2.trans h_assoc)

  use sR_fin
  constructor
  · intro p hp; cases Multiset.mem_add.1 hp with
    | inl h => exact hsR_primes p h
    | inr h => have : p = f := Multiset.eq_of_mem_replicate h; subst this; exact hfprime
  · exact final_associated

--main theorem: Nagata's criterion for UFDs
--Notice that the existence_step is the only nontrivial part of the proof,
--the uniqueness of factorization in R follows directly from the existence of factorizations
theorem nagata_theorem {R T : Type*}
  [CommRing R] [CommRing T] [Algebra R T] [IsDomain R] [IsDomain T]
  [IsNoetherianRing R] (f : R) (hf0 : f ≠ 0) (hfprime : Prime f)
  (hT : IsLocalization.Away (f : R) T) [UniqueFactorizationMonoid T] :
  UniqueFactorizationMonoid R := by
  -- For any nonzero `x : R` factor `algebraMap R T x` in `T` and lift the factors to `R`.
  have existence_step_inst := existence_step (R := R) (T := T) f hf0 hfprime hT
  exact UniqueFactorizationMonoid.of_exists_prime_factors existence_step_inst
