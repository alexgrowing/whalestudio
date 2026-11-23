import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open GroundTheory.Heights₂.Heights InnerProductSpace

universe u v w

noncomputable section

theorem det_gram_re_le_prod_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℂ v) :
    (det (gram ℂ v)).re ≤ ∏ i, ‖v i‖ ^ 2 := by
  set W := Submodule.span ℂ (Set.range v)
  have : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  let w : Fin n → W := fun i ↦ ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hgw : gram ℂ v = gram ℂ w := by
    ext i j
    simp only [gram_apply, w, Submodule.coe_inner]
  have hfin : Module.finrank ℂ W = Fintype.card (Fin n) := finrank_span_eq_card hv
  let b : OrthonormalBasis (Fin n) ℂ W := gramSchmidtOrthonormalBasis hfin w
  have hb : b.toBasis.det w = ∏ i, inner ℂ (b i) (w i) := gramSchmidtOrthonormalBasis_det hfin w
  set A := b.toBasis.toMatrix w
  have hA : gram ℂ w = Aᴴ * A := by
    ext j k
    rw [gram_apply, mul_apply, ← b.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [A, conjTranspose_apply, Module.Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply, RCLike.star_def,
      inner_conj_symm]
  have hdet : (det (gram ℂ w)).re = ‖b.toBasis.det w‖ ^ 2 := by
    rw [hA, det_mul, det_conjTranspose, Module.Basis.det_apply, RCLike.star_def, Complex.conj_mul']
    norm_cast
  rw [hgw, hdet, hb, norm_prod, ← Finset.prod_pow]
  gcongr with i
  calc ‖inner ℂ (b i) (w i)‖ ≤ ‖b i‖ * ‖w i‖ := norm_inner_le_norm _ _
    _ = ‖v i‖ := by rw [b.orthonormal.1 i, one_mul]; rfl

section Gram

variable {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]

theorem log_gramDet_le (h : HermitianMetric K E) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {s : ι → E} (hs : LinearIndependent (𝓞 K) s) :
    Real.log (gramDet h σ s) ≤ 2 * ∑ i, Real.log ‖fibreVec h σ (s i)‖ := by
  let e := Fintype.equivFin ι
  have hs' : LinearIndependent (𝓞 K) (s ∘ e.symm) := hs.comp _ e.symm.injective
  have hne : ∀ i, fibreVec h σ (s i) ≠ 0 := (linearIndependent_fibreVec h σ hs).ne_zero
  have hH := det_gram_re_le_prod_norm_sq (fun i ↦ fibreVec h σ ((s ∘ e.symm) i))
    (linearIndependent_fibreVec h σ hs')
  rw [← gramDet_reindex h σ e.symm s]
  calc Real.log (gramDet h σ (s ∘ e.symm))
      ≤ Real.log (∏ i, ‖fibreVec h σ ((s ∘ e.symm) i)‖ ^ 2) :=
        Real.log_le_log (gramDet_pos h σ hs') hH
    _ = 2 * ∑ i, Real.log ‖fibreVec h σ ((s ∘ e.symm) i)‖ := by
        rw [Real.log_prod (s := Finset.univ) (f := fun i ↦ ‖fibreVec h σ ((s ∘ e.symm) i)‖ ^ 2)
          (fun i _ ↦ pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne (e.symm i)))), Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Real.log_pow]
        push_cast
        ring
    _ = 2 * ∑ i, Real.log ‖fibreVec h σ (s i)‖ := by
        congr 1
        exact e.symm.sum_comp (fun i ↦ Real.log ‖fibreVec h σ (s i)‖)

end Gram

theorem Hadamard.intersectionNumber_baseChange : Hadamard.Statement.{u, v, w} := by
  intro K _ _ M ι _ x La hli hcard hnorm
  classical
  set r := Module.finrank (𝓞 K) M.carrier
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hN : 0 ≤ Real.log (Nat.card (M.carrier ⧸ Submodule.span (𝓞 K) (Set.range x))) :=
    Real.log_natCast_nonneg _
  have hσ : ∀ σ : K →+* ℂ, Real.log (gramDet M.metric σ x) ≤ 2 * (r * Real.log La) := by
    intro σ
    refine (log_gramDet_le M.metric σ hli).trans ?_
    have hle : ∑ i, Real.log ‖fibreVec M.metric σ (x i)‖ ≤ ∑ _i : ι, Real.log La :=
      Finset.sum_le_sum fun i _ ↦ Real.log_le_log
        (norm_pos_iff.mpr ((linearIndependent_fibreVec M.metric σ hli).ne_zero i)) (hnorm i σ)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard] at hle
    linarith
  have hsum : ∑ σ : K →+* ℂ, Real.log (gramDet M.metric σ x) ≤
      Module.finrank ℚ K * (2 * (r * Real.log La)) := by
    calc _ ≤ ∑ _σ : K →+* ℂ, 2 * (r * Real.log La) := Finset.sum_le_sum fun σ _ ↦ hσ σ
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul]
  rw [HermitianBundle.deg, HermitianBundle.arithDegree, arithDegree_eq M.metric hli hcard, degreeWith,
    le_div_iff₀ hd]
  nlinarith

theorem Hadamard.proof (_h1 : Sublattice.Statement.{u, v}) : Hadamard.Statement.{u, v, w} :=
  Hadamard.intersectionNumber_baseChange

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
