module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Category.ModuleCat.Basic

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
