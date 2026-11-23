import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFrameNormEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffDetMemSpanDetIntegralPolynomialVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteHeightSubMeanLeDegreeFullLatticeDetIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HadamardIneqComplexCombinationsBasisStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace GlobalTheory.HSShort.DetTop

theorem exists_rightInv {F : Type} [Field F] {N n : ℕ} (w : Matrix (Fin N) (Fin n) F)
    (hw : Submodule.span F (Set.range w.col) = ⊤) : ∃ w' : Matrix (Fin n) (Fin N) F, w * w' = 1 := by
  have hr : LinearMap.range w.mulVecLin = ⊤ := by
    rw [Matrix.range_mulVecLin]; exact hw
  obtain ⟨g', hg'⟩ := w.mulVecLin.exists_rightInverse_of_surjective hr
  refine ⟨LinearMap.toMatrix' g', ?_⟩
  have := congrArg LinearMap.toMatrix' hg'
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at this
  have e : LinearMap.toMatrix' w.mulVecLin = w := LinearMap.toMatrix'_toLin' w
  rwa [e] at this

theorem linSubst_det {F : Type} [Field F] {B N n d : ℕ} (w : Matrix (Fin N) (Fin n) F)
    (P : Matrix (Fin d) (Fin d) (MvPolynomial (Fin B × Fin N) F)) :
    linSubst w P.det = (P.map (linSubst w)).det := by
  have := RingHom.map_det (aeval (fun p : Fin B × Fin N => ∑ k, C (w p.2 k) * X (p.1, k)) :
    MvPolynomial (Fin B × Fin N) F →ₐ[F] MvPolynomial (Fin B × Fin n) F).toRingHom P
  exact this

end GlobalTheory.HSShort.DetTop

namespace GlobalTheory.HSShort.DetTop

theorem arch {F V : Type} [Field F] [AddCommGroup V] [Module F V] (nm : HermFam F V) {d : ℕ}
    (b : Module.Basis (Fin d) F V) {B N : ℕ} (hN : 0 < N) (σ : F →+* ℂ) (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : A.det ≠ 0) (P : Matrix (Fin d) (Fin d) (MvPolynomial (Fin B × Fin N) F)) (a : Fin B → ℕ)
    (Bd : Fin d → ℝ) (hP : P.det ≠ 0) (hhom : IsMultiHomogeneous a P.det) (hBd : ∀ k, 0 < Bd k)
    (hbd : ∀ k (u : Fin B × Fin N → ℂ), (∀ i, frameNorm A (fun j => u (i, j)) = 1) →
      cnrm nm σ (fun i => eval₂ σ u (P i k)) b ≤ Bd k) :
    blockSphereMean B N (linSubst A (map σ P.det)) ≤
      ∑ k, Real.log (Bd k) - Real.log (nm.gram σ b).det.re / 2 := by
  haveI := blockSphereMeasure_isProbability (B := B) hN
  have hmap0 : map σ P.det ≠ 0 := fun h =>
    hP (MvPolynomial.map_injective σ σ.injective (by rw [h, map_zero]))
  have hf0 : linSubst A (map σ P.det) ≠ 0 :=
    GlobalTheory.HeightUnique.linSubst_ne_zero (Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.2 hA)) hmap0
  have hfm : IsMultiHomogeneous a (linSubst A (map σ P.det)) :=
    GlobalTheory.HeightUnique.linSubst_homog A (isMultiHomogeneous_map_ring a _ hhom σ)
  have hint := Closed.sphereLogIntegrable B N a _ hf0 hfm
  have hae := ae_blockSphere_eval_ne_zero B N a _ hf0 hfm
  have hpt : ∀ z : BlockSphere B N, eval (blockPoint z) (linSubst A (map σ P.det)) ≠ 0 →
      Real.log ‖eval (blockPoint z) (linSubst A (map σ P.det))‖ ≤
        ∑ k, Real.log (Bd k) - Real.log (nm.gram σ b).det.re / 2 := by
    intro z hz
    set u : Fin B × Fin N → ℂ := fun q => A.mulVec (fun k => blockPoint z (q.1, k)) q.2 with hu
    have hunit : ∀ i, frameNorm A (fun j => u (i, j)) = 1 := fun i => by
      show frameNorm A (A.mulVec (fun k => blockPoint z (i, k))) = 1
      rw [GlobalTheory.MaxPoint.frameNorm_mulVec hA]
      have hz := (z i).2
      rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq] at hz
      simpa [blockPoint, spherePoint] using hz
    have hev : eval (blockPoint z) (linSubst A (map σ P.det)) = (Matrix.of fun i k => eval₂ σ u (P i k)).det := by
      rw [GlobalTheory.MaxPoint.eval_linSubst, MvPolynomial.eval_map]
      have := RingHom.map_det (eval₂Hom σ u) P
      rw [coe_eval₂Hom] at this
      rw [this]; rfl
    rw [hev] at hz ⊢
    obtain ⟨hG, hH⟩ := GlobalTheory.T.hadamard_ineq_complex_combinations_basis F V nm d b σ (Matrix.of fun i k => eval₂ σ u (P i k))
    have hprod : ∏ k, cnrm nm σ (fun i => (Matrix.of fun i k => eval₂ σ u (P i k)) i k) b ≤ ∏ k, Bd k :=
      Finset.prod_le_prod (fun k _ => Real.sqrt_nonneg _) (fun k _ => hbd k u hunit)
    have hpos : 0 < ‖(Matrix.of fun i k => eval₂ σ u (P i k)).det‖ := norm_pos_iff.2 hz
    have hsq : 0 < Real.sqrt (nm.gram σ b).det.re := Real.sqrt_pos.2 hG
    have hle := Real.log_le_log (mul_pos hpos hsq) (hH.trans hprod)
    rw [Real.log_mul hpos.ne' hsq.ne', Real.log_prod (fun k _ => (hBd k).ne'), Real.log_sqrt hG.le] at hle
    linarith
  unfold blockSphereMean
  calc ∫ z, Real.log ‖eval (blockPoint z) (linSubst A (map σ P.det))‖ ∂(blockSphereProb B N)
      ≤ ∫ _z, (∑ k, Real.log (Bd k) - Real.log (nm.gram σ b).det.re / 2) ∂(blockSphereProb B N) :=
        integral_mono_ae hint (integrable_const _) (by
          filter_upwards [hae] with z hz
          exact hpt z hz)
    _ = _ := by simp

end GlobalTheory.HSShort.DetTop

theorem GlobalTheory.HSShort.deg_ge_ht_det : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (nm : HermFam F V) (M : Submodule (𝓞 F) V) (d : ℕ) (b : Module.Basis (Fin d) F V), IsFull M → ∀ (B N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (Λ : ℝ), Lat w A Λ → ∀ (P : Matrix (Fin d) (Fin d) (MvPolynomial (Fin B × Fin N) F)) (a : Fin B → ℕ) (Bd : Fin d → ℝ), P.det ≠ 0 → IsMultiHomogeneous a P.det → (∀ k, 0 < Bd k) → (∀ k m, ∑ i, coeff m (linSubst w (P i k)) • b i ∈ M) → (∀ k σ (u : Fin B × Fin N → ℂ), (∀ i, frameNorm (A σ) (fun j => u (i, j)) = 1) → cnrm nm σ (fun i => eval₂ σ u (P i k)) b ≤ Bd k) → ht w A P.det - ∑ k, Real.log (Bd k) ≤ deg nm M := by
  intro F V _ _ _ _ _ _ nm M d b hM B N n w A Λ hL P a Bd hP hhom hBd hcoef hbd
  obtain ⟨w', hw'⟩ := GlobalTheory.HSShort.DetTop.exists_rightInv w hL.spans
  have hdet := GlobalTheory.HSShort.DetTop.linSubst_det w P
  have hg0 : linSubst w P.det ≠ 0 := GlobalTheory.HeightUnique.linSubst_ne_zero hw' hP
  have hcg : ∀ m, coeff m (linSubst w P.det) ∈
      Submodule.span (𝓞 F) {y | ∃ v : Fin d → V, (∀ i, v i ∈ M) ∧ y = b.det v} := by
    rw [hdet]
    exact GlobalTheory.T.coeff_det_mem_span_det_integral_polynomial_vectors F V M d b _ (P.map (linSubst w)) (fun k m => by simpa using hcoef k m)
  have hfin := GlobalTheory.T.finiteHeight_sub_mean_le_degree_fullLattice_detIdeal F V nm M d b hM _ _ hg0 hcg
  have harch : ∀ σ, blockSphereMean B N (linSubst (A σ) (map σ P.det)) ≤
      ∑ k, Real.log (Bd k) - Real.log (nm.gram σ b).det.re / 2 := fun σ =>
    GlobalTheory.HSShort.DetTop.arch nm b hL.pos σ (A σ) (hL.det σ) P a Bd hP hhom hBd (fun k u hu => hbd k σ u hu)
  have hr : (0 : ℝ) < Module.finrank ℚ F := by exact_mod_cast Module.finrank_pos
  have hcard : (Fintype.card (F →+* ℂ) : ℝ) = Module.finrank ℚ F := by
    exact_mod_cast NumberField.Embeddings.card F ℂ
  have hht : ht w A P.det = finPart (linSubst w P.det) +
      mean F (fun σ => blockSphereMean B N (linSubst (A σ) (map σ P.det))) := by
    simp only [ht, formHeight, finPart, mean, Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero]
    rw [add_div]
  have hmean : mean F (fun σ => blockSphereMean B N (linSubst (A σ) (map σ P.det))) ≤
      ∑ k, Real.log (Bd k) - mean F (fun σ => Real.log (nm.gram σ b).det.re) / 2 := by
    unfold mean
    calc (∑ σ, blockSphereMean B N (linSubst (A σ) (map σ P.det))) / (Module.finrank ℚ F : ℝ)
        ≤ (∑ σ : F →+* ℂ, (∑ k, Real.log (Bd k) - Real.log (nm.gram σ b).det.re / 2)) / (Module.finrank ℚ F : ℝ) :=
          div_le_div_of_nonneg_right (Finset.sum_le_sum fun σ _ => harch σ) hr.le
      _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, ← Finset.sum_div]
          field_simp
  rw [hht]
  linarith
