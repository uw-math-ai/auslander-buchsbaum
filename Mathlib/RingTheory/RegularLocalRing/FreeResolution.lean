module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.Determinant

/-!
# Projective resolutions

A projective resolution `P : ProjectiveResolution Z` of an object `Z : C` consists of
an `ℕ`-indexed chain complex `P.complex` of projective objects,
along with a quasi-isomorphism `P.π` from `C` to the chain complex consisting just
of `Z` in degree zero.

-/

@[expose] public section

universe u v

namespace CategoryTheory

open Category Limits ChainComplex HomologicalComplex ModuleCat TensorProduct

variable {R : Type*} [CommRing R]
variable (M : Type*) [AddCommGroup M] [Module R M]
example : ModuleCat R := of R M

/--
A `ProjectiveResolution Z` consists of a bundled `ℕ`-indexed chain complex of projective objects,
along with a quasi-isomorphism to the complex consisting of just `Z` supported in degree `0`.
-/
-- structure FiniteFreeResolution (M : Type*) [AddCommGroup M] [Module R M] where
--   /-- the chain complex involved in the resolution -/
--   complex : ChainComplex (ModuleCat R) ℕ
--   /-- the chain complex must be degreewise projective -/
--   projective : ∀ n, Projective (complex.X n) := by infer_instance
--   /-- the morphism to the single chain complex with `Z` in degree `0` -/
--   π : complex ⟶ (ChainComplex.single₀ (ModuleCat R)).obj (of R M)
--   /-- the morphism to the single chain complex with `Z` in degree `0` is a quasi-isomorphism -/
--   quasiIso : QuasiIso π := by infer_instance


instance : CategoryWithHomology (ModuleCat R) := sorry

example (com : ChainComplex (ModuleCat R) ℕ) : ∀ i : ℕ, HasHomology com i := inferInstance


/-
  Define the determinant of a module, show that the determinant is additive
-/
section Determinant

variable (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]

open Module TensorProduct

noncomputable
def det := ⋀[R]^(finrank R M) M

/-
  I don't think this is true as written, but it should be true if
  we add finite rank and locally free hypotheses
-/
def det_additive {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    (det R S.X₁) ⊗[R] (det R S.X₂) ≃ₗ[R] det R S.X₂ := sorry
  -- this one will be hard

-- helper lemma for det free - top wedge product of basis vectors is non-zero
lemma wedge_ne_zero [Nontrivial R] [Module.Free R M] [Module.Finite R M]
    [StrongRankCondition R] :
    let b := Module.Free.chooseBasis R M
    let e := Fintype.equivFinOfCardEq (finrank_eq_card_chooseBasisIndex R M).symm
    (exteriorPower.ιMulti R (finrank R M)) (fun i => b (e.symm i)) ≠ 0 := by
  intro b e
  let bFin : Basis (Fin (finrank R M)) R M := b.reindex e
  let f := exteriorPower.alternatingMapLinearEquiv bFin.det
  intro h
  have hf_wedge : f ((exteriorPower.ιMulti R (finrank R M)) (fun i => b (e.symm i))) =
      bFin.det (fun i => b (e.symm i)) :=
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti bFin.det (fun i => b (e.symm i))
  have hf_wedge_zero : f ((exteriorPower.ιMulti R (finrank R M)) (fun i => b (e.symm i))) = 0 := by
    rw [h]; simp
  have hdet_ne_zero : bFin.det (fun i => b (e.symm i)) ≠ 0 := by
    have : (fun i => b (e.symm i)) = ⇑bFin := by
      ext i
      simp [bFin, Basis.reindex]
    rw [this]
    exact (AlternatingMap.map_basis_ne_zero_iff bFin bFin.det).mpr bFin.det_ne_zero
  exact hdet_ne_zero (hf_wedge ▸ hf_wedge_zero)


-- !!! ADDED STRONG RANK CONDITION, WHICH ONLY WORKS IF THE COMM RING IS NON-TRIVIAL AND NON TRIV R
theorem det_free [Module.Free R M] [Module.Finite R M] [StrongRankCondition R] [Nontrivial R] :
    Module.Free R (det R M) := by
  let b := Module.Free.chooseBasis R M
  have hrank : finrank R M = Fintype.card (Module.Free.ChooseBasisIndex R M) :=
    finrank_eq_card_chooseBasisIndex R M
  let e : Module.Free.ChooseBasisIndex R M ≃ Fin (finrank R M) :=
    Fintype.equivFinOfCardEq hrank.symm
  let wedge : det R M :=
    (exteriorPower.ιMulti R (finrank R M)) (fun i => b (e.symm i))
  have hwedge_ne_zero : wedge ≠ 0 := wedge_ne_zero R M
  have hli : LinearIndependent R (fun _ : Fin 1 => wedge) := by
    sorry
    --shows {wedge} is lin indep
  have hspan : ⊤ ≤ Submodule.span R (Set.range (fun _ : Fin 1 => wedge)) := by
    simp only [Set.range_const]
    -- shows wedge spans all of det R M,
    sorry
  exact Module.Free.of_basis (Basis.mk hli hspan)


-- free is a statement that there eixts a basis
--free means get a basis
-- since module is finite, basis is finite, use a have statement for this
--write down ur single element, and then a have statement that u can make a basis
-- show that wedge product of all ur basis elements is a basis

end Determinant

section PiTensor

variable (R : Type u) [CommRing R]



#check PiTensorProduct.tmulEquiv
#check Module.Free.tensor
#check Module.dual_free

/-
  Annoying lemma: if you take a finite indexed tensor product of
  free modules you get a free module.
  Should follow from induction and the two above lemmas
  Free.tensor, tmulEquiv
-/

theorem PiTensorProduct.Free {n : ℕ} (ι : Fin n → Type u) [∀ i, AddCommGroup (ι i)]
    [∀ i, Module R (ι i)] (hFree : ∀ i, Module.Free R (ι i)) : Module.Free R (⨂[R] i, ι i) := by
  induction n with
  /- By convention, the empty tensor product is the base ring R -/
  | zero =>
  exact Module.Free.of_equiv' (Module.Free.self R) ((PiTensorProduct.isEmptyEquiv (Fin 0)).symm)
  | succ n hn =>
  specialize hn (fun n => ι ⟨n, by simp⟩)
  specialize hn ?_
  · intro i
    apply hFree
  /- Prove equiv: (⨂ Fin n, ι) ⊗ ι n ≃ ⨂ Fin (n+1), ι -/
  let H : (⨂[R] (i : Fin n), ι ⟨i, by simp⟩) ⊗[R] (ι ⟨n, by simp⟩) ≃ₗ[R]
      (⨂[R] (i : Fin (n + 1)), ι i) :=
    /- (1) Show ι n ≃ ⨂ (Fin 1), ι using subsingletonEquiv and apply to right factor of tensor -/
    (LinearEquiv.lTensor _
      (PiTensorProduct.subsingletonEquiv
        (s := fun j => ι (finSumFinEquiv (Sum.inr j))) (0 : Fin 1)).symm).trans
      /- (2) merge the two tensor products using tmulEquivDep, then reindex. -/
      ((PiTensorProduct.tmulEquivDep R (fun i => ι (finSumFinEquiv i))).trans
        (PiTensorProduct.reindex R ι finSumFinEquiv.symm).symm)
  apply Module.Free.of_equiv' ?_ H
  apply Module.Free.tensor

end PiTensor


/-
  I want to express that if an invertible module has a finite free resolution,
  then it is actually free
-/
section FiniteFreeRes

open Module


variable (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]

structure FiniteFreeResolution (n : ℕ) where
  /-- the chain complex involved in the resolution -/
  complex : ChainComplex (ModuleCat R) ℕ
  π : complex ⟶ (ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R M)
  /-- the morphism to the single chain complex with `Z` in degree `0` is a quasi-isomorphism -/
  quasiIso : QuasiIso π := by infer_instance
  finite : ∀ n, Module.Finite R (complex.X n)
  free : ∀ n, Free R (complex.X n)
  bounded : ∃ N, ∀ n > N, IsZero (complex.X n)

/-
  Disgusting code: if _ then M else N doesn't have a R-Module instance,
  despite M and N having R-Module instances
-/
instance (P : Prop) [hP : Decidable P] (M N : Type u) [AddCommGroup M] [AddCommGroup N] :
    AddCommGroup (if P then M else N) :=
  match hP with
  | isFalse h => by simp only [h, ↓reduceIte]; infer_instance
  | isTrue h => by simp only [h, ↓reduceIte]; infer_instance

instance (P : Prop) [hP : Decidable P] (M N : Type u) [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] : Module R (if P then M else N) :=
  match hP with
  | isFalse h => by simp only [h, ↓dreduceIte]; infer_instance
  | isTrue h => by simp only [h, ↓dreduceIte]; infer_instance

/- The alternating sum of determinants of modules in a finite free resolution -/
abbrev detC {n : ℕ} (C : FiniteFreeResolution R M n) :=
  ⨂[R] (i : Fin n), if (i.val % 2 = 0) then det R (C.complex.X i)
      else Dual R (det R (C.complex.X i))


#check ite
/-
  I think this statement should be correct: if an invertible M admits a finite
  free resolution, then M is free.
  I need a better way to define the
-/
-- !!! ADDED STRONG RANK CONDITION, WHICH ONLY WORKS IF THE COMM RING IS NON-TRIVIAL
theorem free_of_finite_free_res (hM : Module.Invertible R M) {n : ℕ}
    [StrongRankCondition R] [Nontrivial R]
    (h : Nonempty (FiniteFreeResolution R M n)) : Free R M := by
  obtain ⟨C⟩ := h
  have H : detC R M C ≃ₗ[R] M := sorry
  refine Free.of_equiv' ?_ H
  apply PiTensorProduct.Free
  intro i
  by_cases h : (i.val % 2 = 0)
  . sorry
  -- . suffices Free R (det R (C.complex.X i)) from (?_)
  --   . have HH : ((if ↑i % 2 = 0 then ↥(det R ↑(C.complex.X ↑i)) else Dual R ↥(det R ↑(C.complex.X ↑i)))) =
  --       ↥(det R ↑(C.complex.X ↑i)) := by
  --     . sorry
  --     sorry
  --   . apply det_free _ _ (C.free _) (C.finite _)
  . sorry

end FiniteFreeRes
