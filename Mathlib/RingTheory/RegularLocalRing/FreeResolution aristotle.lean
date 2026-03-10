import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Determinant

/-!
# Projective resolutions

A projective resolution `P : ProjectiveResolution Z` of an object `Z : C` consists of
an `ℕ`-indexed chain complex `P.complex` of projective objects,
along with a quasi-isomorphism `P.π` from `C` to the chain complex consisting just
of `Z` in degree zero.

-/

@[expose] section

universe u v

namespace CategoryTheory

open Category Limits ChainComplex HomologicalComplex ModuleCat TensorProduct

variable {R : Type*} [CommRing R]

variable (M : Type*) [AddCommGroup M] [Module R M]

example : ModuleCat R := of R M

/-
  Define the determinant of a module, show that the determinant is additive
-/
section Determinant

variable (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]

open Module TensorProduct

noncomputable
def det := ⋀[R]^(finrank R M) M

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

/-
For any alternating map `f` from `M^n` to `N`, `f(v) = det(v) • f(e)` where `e` is a basis.
-/
theorem AlternatingMap.apply_eq_smul_det_of_basis {R : Type u} [CommRing R]
    {M : Type u} [AddCommGroup M] [Module R M]
    {N : Type u} [AddCommGroup N] [Module R N]
    {n : ℕ} (e : Basis (Fin n) R M) (f : M [⋀^Fin n]→ₗ[R] N)
    (v : Fin n → M) : f v = (e.det v) • f e := by
  -- By definition of determinant, we can write v as a linear combination of the basis vectors.
  obtain ⟨A, hA⟩ : ∃ A : Fin n → Fin n → R, v = fun i => ∑ j, A i j • e j := by
    exact ⟨ fun i j => e.repr ( v i ) j, by ext i; simp only [ e.sum_repr ] ⟩
  -- By definition of determinant, we can write
  -- the alternating multilinear map $f$ in terms of
  -- the determinant of $A$.
  have h_det : ∀ (σ : Equiv.Perm (Fin n)), f (fun i => e (σ i)) = (Equiv.Perm.sign σ) • f e := by
    intro σ; exact (by
    convert f.map_perm _ σ using 1)
  -- By definition of determinant, we can expand $f(v)$ as a sum over permutations.
  have h_expand : f v = ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ) • (∏ i, A i (σ i)) • f e := by
    -- Apply the linearity of $f$ to expand $f(v)$.
    have h_expand : f v = ∑ σ : Fin n → Fin n, (∏ i, A i (σ i)) • f (fun i => e (σ i)) := by
      rw [ hA ]
      convert f.map_sum fun i j => A i j • e j using 1
      simp +decide [MultilinearMap.map_smul_univ]
    -- Since $f$ is alternating, $f(e_{\sigma(0)}, \ldots, e_{\sigma(n-1)}) = 0$
    -- if $\sigma$ is not a permutation.
    have h_zero : ∀ σ : Fin n → Fin n, ¬Function.Bijective σ → f (fun i => e (σ i)) = 0 := by
      intro σ hσ
      -- Since $\sigma$ is not bijective, there exist $i \ne j$ such that $\sigma(i) = \sigma(j)$.
      obtain ⟨i, j, hij, h_eq⟩ : ∃ i j : Fin n, i ≠ j ∧ σ i = σ j := by
        contrapose! hσ
        exact ⟨ fun x y hxy => Classical.not_not.1 fun h => hσ x y h hxy,
          Finite.injective_iff_surjective.1 fun x y hxy =>
            Classical.not_not.1 fun h => hσ x y h hxy ⟩
      exact
        AlternatingMap.map_eq_zero_of_not_injective f (fun i ↦ e (σ i)) fun a ↦
          hij (a (congrArg (⇑e) h_eq))
    rw [ h_expand, ← Finset.sum_subset ( Finset.subset_univ
      ( Finset.image ( fun σ : Equiv.Perm ( Fin n ) => ⇑σ ) Finset.univ ) ) ]
    · rw [ Finset.sum_image ];
      · -- By substituting h_det into each term of the sum, we can factor out the sign of σ.
        apply Finset.sum_congr rfl
        intro σ _
        rw [h_det σ];
        rw [ SMulCommClass.smul_comm ]
      · exact fun σ _ τ _ h => Equiv.Perm.ext fun i => by simpa using congr_fun h i;
    · simp only [Finset.mem_univ, Finset.mem_image, true_and, not_exists, forall_const]
      exact fun σ hσ => by rw [ h_zero σ fun h => hσ ( Equiv.ofBijective σ h ) rfl, smul_zero ]
  simp_all only
  simp only [e.det_apply, Matrix.det_apply', Finset.sum_smul,
    Module.Basis.toMatrix_apply, map_sum, map_smul,
    Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
    mul_one, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.single_apply]
  exact Finset.sum_congr rfl fun _ _ =>
    by rcases Int.units_eq_one_or ( Equiv.Perm.sign ‹_› ) with h | h <;> simp +decide [ h ] ;

theorem exteriorPower.exists_dual_map_eq_one {R : Type u} [CommRing R]
    {M : Type u} [AddCommGroup M] [Module R M]
    {n : ℕ} (e : Basis (Fin n) R M) :
    ∃ φ : (⋀[R]^n M) →ₗ[R] R, φ (exteriorPower.ιMulti R n e) = 1 := by
  by_contra! h_contra
  convert h_contra ( exteriorPower.alternatingMapLinearEquiv ( e.det ) ) ?_
  simp [ Module.Basis.det_self ]


-- If all else fails we can have det_free just for Noetherian rings because of
#check IsNoetherianRing.strongRankCondition

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
    -- Since the function from Fin 1 to the wedge product is
    -- just the constant function that inputs wedge,
    -- and wedge is non-zero, the linear independence
    -- follows directly from the definition of linear
    -- independence for a single element.
    simp only [linearIndependent_iff', Fin.forall_fin_one, Fin.isValue]
    intro s g hg hs; fin_cases s <;> simp_all
    -- Since `wedge` is non-zero, there exists a linear map
    -- `φ : det R M → R` such that `φ(wedge) = 1`.
    obtain ⟨φ, hφ⟩ : ∃ φ : (CategoryTheory.det R M) →ₗ[R] R, φ wedge = 1 := by
      have := exteriorPower.exists_dual_map_eq_one ( b.reindex e )
      aesop
    simpa [ hφ ] using congr_arg φ hg
    --shows {wedge} is lin indep
  have hspan : ⊤ ≤ Submodule.span R (Set.range (fun _ : Fin 1 => wedge)) := by
    simp only [Set.range_const]
    -- shows wedge spans all of det R M,
    -- Any element in the image of `exteriorPower.ιMulti` is of the form `exteriorPower.ιMulti(v)`.
    -- By `AlternatingMap.apply_eq_smul_det_of_basis` applied
    -- to the alternating map `exteriorPower.ιMulti`
    -- (viewed as taking values in `det R M`),
    -- we have `exteriorPower.ιMulti v = (b.det v) • wedge`.
    have h_image_span : ∀ v : Fin (Module.finrank R M) → M, exteriorPower.ιMulti R
        (Module.finrank R M) v ∈ Submodule.span R {wedge} := by
      intro v
      have hv : exteriorPower.ιMulti R (Module.finrank R M)
          v = (b.det (fun i => v (e i))) • wedge := by
        convert AlternatingMap.apply_eq_smul_det_of_basis ( b.reindex e )
          ( exteriorPower.ιMulti R ( Module.finrank R M ) ) v using 1
        simp only [Basis.coe_reindex, Basis.det_apply]
        convert rfl
        rw [ ← Matrix.det_reindex_self e.symm ]
        congr! 1
        ext i j
        simp [ b.toMatrix_apply ]
      exact hv ▸ Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    rw [ ← exteriorPower.ιMulti_span ]
    exact Submodule.span_le.mpr ( Set.range_subset_iff.mpr h_image_span )
  exact Module.Free.of_basis (Basis.mk hli hspan)

end Determinant

end CategoryTheory

end
