module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
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


namespace CategoryTheory

open Category Limits ChainComplex HomologicalComplex ModuleCat

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

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

open Module TensorProduct

noncomputable
def det := ⋀[R]^(finrank R M) M

--TODO: add finiteness, projectiveness hypotheses so this is actually true
def det_additive {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    (det R S.X₁) ⊗[R] (det R S.X₂) ≃ₗ[R] det R S.X₂ := sorry

end Determinant


/-
  I want to express that if an invertible module has a finite free resolution,
  then it is actually free
-/
section FiniteFreeRes

open Module

#check Module.Free.tensor
#check Module.dual_free

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

structure FiniteFreeResolution (n : ℕ) where
  /-- the chain complex involved in the resolution -/
  complex : ChainComplex (ModuleCat R) ℕ
  acyclic : complex.Acyclic
  /-- the chain complex must be degreewise projective -/
  zero : complex.X 0 = M
  finite : ∀ n > 0, Module.Finite R (complex.X n)
  free : ∀ n > 0, Free R (complex.X n)
  bounded : ∃ N, ∀ n > N, IsZero (complex.X n)

variable (S : FiniteFreeResolution R M 5)

theorem free_of_finite_free_res (hM : Module.Invertible R M) {n : ℕ}
    (h : Nonempty (FiniteFreeResolution R M n)) : Free R M := sorry

end FiniteFreeRes
