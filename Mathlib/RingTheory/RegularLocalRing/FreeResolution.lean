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

theorem det_free (hFree : Free R M) (hFinite : Module.Finite R M) : Free R (det R M) := sorry

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
  I think this statement should be correct: if an invertible M admits a finite
  free resolution, then M is free.
  I need a better way to define the
-/
theorem free_of_finite_free_res (hM : Module.Invertible R M) {n : ℕ}
    (h : Nonempty (FiniteFreeResolution R M n)) : Free R M := by
  obtain ⟨C⟩ := h
  let detC := ⨂[R] (i : Fin n), det R (C.complex.X i)
  have H : detC ≃ₗ[R] M := sorry
  refine Free.of_equiv' ?_ H
  apply PiTensorProduct.Free
  intro i
  apply det_free R _ (C.free _) (C.finite _)

#check ⨂[R] _, M

end FiniteFreeRes
