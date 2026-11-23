import Mathlib
import ReciprocityTheory.SemistableReduction.AlgAll

namespace ReciprocityTheory.ChartRestriction.G.T0

namespace HDiscLat

open Module

theorem det_blockDiagonal' {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    {κ : ι → Type*} [∀ c, Fintype (κ c)] [∀ c, DecidableEq (κ c)]
    (M : ∀ c, Matrix (κ c) (κ c) R) :
    (Matrix.blockDiagonal' M).det = ∏ c, (M c).det := by
  classical

  have hblk : ∀ c, (Matrix.toSquareBlock (Matrix.blockDiagonal' M) Sigma.fst c).det =
      (M c).det := by
    intro c
    let e : κ c ≃ {s : (Σ c, κ c) // s.1 = c} :=
      { toFun := fun k => ⟨⟨c, k⟩, rfl⟩
        invFun := fun s => cast (congrArg κ s.2) s.1.2
        left_inv := fun k => rfl
        right_inv := by
          rintro ⟨⟨a, k⟩, rfl⟩
          rfl }
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    ext k k'
    show Matrix.blockDiagonal' M ⟨c, k⟩ ⟨c, k'⟩ = M c k k'
    first
      | exact Matrix.blockDiagonal'_apply_eq M c k k'
      | simp [Matrix.blockDiagonal'_apply]
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  first
    | rw [(Matrix.blockTriangular_blockDiagonal' M).det]
    | rw [Matrix.BlockTriangular.det (Matrix.blockTriangular_blockDiagonal' M)]
  rw [Finset.prod_congr rfl (fun c _ => hblk c)]
  refine Finset.prod_subset (Finset.subset_univ _) ?_
  intro c _ hc
  haveI : IsEmpty (κ c) :=
    ⟨fun k => hc (Finset.mem_image.2 ⟨⟨c, k⟩, Finset.mem_univ _, rfl⟩)⟩
  exact Matrix.det_isEmpty

theorem gram_mul {F L : Type*} [Field F] [Field L] [Algebra F L] {κ : Type*} [Fintype κ]
    [DecidableEq κ] (a : Basis κ F L) (h : L) :
    (Matrix.of fun p q => Algebra.trace F L (h * a p * a q)).det =
      Algebra.norm F h * Algebra.discr F a := by

  rw [Algebra.discr_def, Algebra.norm_eq_matrix_det a h,
    ← Matrix.det_transpose (Algebra.leftMulMatrix a h), ← Matrix.det_mul]
  congr 1
  ext p q
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.leftMulMatrix_eq_repr_mul]
  conv_lhs => rw [← a.sum_repr (h * a p)]
  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [smul_mul_assoc, map_smul, smul_eq_mul]

theorem length_quot {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ)
    {CC V : Type*} [AddCommGroup CC] [Module R CC] [AddCommGroup V] [Module R V]
    {κ : Type*} [Fintype κ] [DecidableEq κ] (α : Basis κ R CC) (φ : CC →ₗ[R] V)
    (hφ : Function.Injective φ) (SA : Submodule R V) (hSA : SA = LinearMap.range φ)
    {m : ℕ} (b' : Fin m → CC) (hli : LinearIndependent R b') (σ : κ ≃ Fin m) :
    ∃ n : ℕ, ∃ u : Rˣ,
      Module.length R (SA ⧸ (Submodule.span R (Set.range (φ ∘ b'))).comap SA.subtype) = n ∧
      α.det (b' ∘ σ) = u * ϖ ^ n := by
  classical
  set N := Submodule.span R (Set.range b')
  have hrank : finrank R N = finrank R CC := by
    rw [finrank_span_eq_card hli, finrank_eq_card_basis α, Fintype.card_fin, Fintype.card_congr σ,
      Fintype.card_fin]
  set s := Submodule.smithNormalFormCoeffs α hrank
  have hlen : Module.length R (CC ⧸ N) = ∑ i, IsDiscreteValuationRing.addVal R (s i) := by
    rw [(Submodule.quotientEquivPiSpan N α hrank).length_eq, Module.length_pi_of_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Ring.ord_eq_addVal]
    rfl
  have hdet : Associated (α.det (b' ∘ σ)) (∏ i, s i) := by
    have key := ReciprocityTheory.MultiplicativeHeights.det_subtype_comp_associated_prod α N hrank (α.equiv (Basis.span hli) σ)
    convert key using 1
    rw [← LinearMap.det_toMatrix α, Basis.det_apply]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, Basis.toMatrix_apply]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Basis.equiv_apply,
      Submodule.subtype_apply]
    rw [Module.Basis.span_apply]
  have hne : (∏ i, s i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => Submodule.smithNormalFormCoeffs_ne_zero α hrank i
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
  have hval : ∑ i, IsDiscreteValuationRing.addVal R (s i) = n := by
    rw [← ReciprocityTheory.MultiplicativeHeights.addVal_prod, hu, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ]
    simp
  let E : CC ≃ₗ[R] SA := (LinearEquiv.ofInjective φ hφ).trans (LinearEquiv.ofEq _ _ hSA.symm)
  have hE : ∀ y, (E y : V) = φ y := fun y => rfl
  have hmap : N.map (E : CC →ₗ[R] SA) =
      (Submodule.span R (Set.range (φ ∘ b'))).comap SA.subtype := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    rw [Set.range_comp, ← Submodule.map_span]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change φ y ∈ _
      exact Submodule.mem_map_of_mem hy
    · rintro ⟨y, hy, hyx⟩
      exact ⟨y, hy, Subtype.ext (by change φ y = _; exact hyx)⟩
  obtain ⟨v, hv⟩ := hdet.symm
  refine ⟨n, u * v, ?_, ?_⟩
  · rw [← (Submodule.Quotient.equiv N _ E hmap).length_eq, hlen, hval]
  · rw [← hv, hu, Units.val_mul]
    ring

end HDiscLat

end ReciprocityTheory.ChartRestriction.G.T0
