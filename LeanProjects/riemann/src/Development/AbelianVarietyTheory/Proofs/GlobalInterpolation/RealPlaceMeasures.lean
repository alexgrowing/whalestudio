import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ActionCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeasurePreservingGlue
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsCompactMatrixEntryAbsSumSublevel
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PositiveDefiniteUnitSphereMassProof
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian

noncomputable section

namespace GlobalTheory.RealPlaceMeasuresProof

open MeasureTheory FourierTransform Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal NNReal

theorem selfDual_of_map {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure V) (hμ : μ.IsAddHaarMeasure) (β : V → V → ℝ) (hs : ∀ x y, β x y = β y x)
    (T : V ≃L[ℝ] E) (R : V → E) (hRm : MeasurableEmbedding R)
    (hR : ∀ x y, β x y = inner ℝ (T x) (R y)) (a b : ℝ≥0) (hab : a * b = 1)
    (hT : μ.map T = a • (volume : Measure E)) (hRv : μ.map R = b • (volume : Measure E)) :
    SelfDual μ (fun x y => Complex.exp (2 * Real.pi * Complex.I * ((β x y : ℝ) : ℂ))) := by
  have gen : ∀ (S : V → E) (c : ℝ≥0), c ≠ 0 → MeasurableEmbedding S →
      μ.map S = c • (volume : Measure E) →
      (∀ g : E → ℂ, ∫ x, g (S x) ∂μ = ((c : ℝ) : ℂ) * ∫ w, g w) ∧
      ∀ g : E → ℂ, Integrable (fun x => g (S x)) μ ↔ Integrable g := by
    intro S c hc he h
    refine ⟨fun g => ?_, fun g => ?_⟩
    · rw [← he.integral_map, h, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    · have := he.integrable_map_iff (μ := μ) (g := g)
      rw [h] at this
      refine this.symm.trans ?_
      exact integrable_smul_measure (by exact_mod_cast hc) ENNReal.coe_ne_top
  have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one hab
  have hb : b ≠ 0 := right_ne_zero_of_mul_eq_one hab
  obtain ⟨haI, haG⟩ := gen T a ha T.toHomeomorph.measurableEmbedding hT
  obtain ⟨hbI, hbG⟩ := gen R b hb hRm hRv
  have ha' : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha
  have hab' : ((a : ℝ) : ℂ) * ((b : ℝ) : ℂ) = 1 := by exact_mod_cast hab
  have key : ∀ (Φ : V → ℂ) (y : V),
      ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((β x y : ℝ) : ℂ)) ∂μ =
        ((a : ℝ) : ℂ) * 𝓕⁻ (fun w => Φ (T.symm w)) (R y) := by
    intro Φ y
    rw [Real.fourierInv_eq', ← haI]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ContinuousLinearEquiv.symm_apply_apply, smul_eq_mul, hR]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  refine ⟨hμ, fun Φ hc hsup hF z => ?_⟩
  have hi : Integrable Φ μ := hc.integrable_of_hasCompactSupport hsup
  simp only [key Φ] at hF ⊢
  have hf : Integrable (fun w => Φ (T.symm w)) := by
    rw [← haG]; simpa using hi
  have hF' : Integrable (𝓕⁻ (fun w => Φ (T.symm w))) := by
    rw [← hbG]
    simpa [← mul_assoc, ha'] using hF.const_mul ((a : ℝ) : ℂ)⁻¹
  have h1 : 𝓕⁻ (fun w => Φ (T.symm w)) = 𝓕 (fun w => Φ (T.symm (-w))) :=
    Real.fourierInv_eq_fourier_comp_neg _
  have h2 : 𝓕⁻ (𝓕 (fun w => Φ (T.symm (-w)))) = fun w => Φ (T.symm (-w)) :=
    Continuous.fourierInv_fourier_eq (by fun_prop) hf.comp_neg (h1 ▸ hF')
  have h3 := congrFun h2 (T z)
  rw [← h1, Real.fourierInv_eq'] at h3
  simp only [map_neg, ContinuousLinearEquiv.symm_apply_apply] at h3
  rw [← h3, ← one_mul (∫ v : E, _), ← hab', mul_assoc ((a : ℝ) : ℂ), ← hbI, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [smul_eq_mul]
  rw [hs y z, hR, real_inner_comm, mul_assoc ((a : ℝ) : ℂ)]
  congr 1
  rw [mul_comm]
  congr 2
  push_cast
  ring

theorem selfDual_line {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    SelfDual (volume : Measure ℝ)
      (fun t s : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((ε * (t * s) : ℝ) : ℂ))) := by
  rcases hε with rfl | rfl
  · exact selfDual_of_map volume inferInstance (fun t s => 1 * (t * s)) (fun x y => by ring)
      (ContinuousLinearEquiv.refl ℝ ℝ) id MeasurableEmbedding.id (fun x y => by simp [mul_comm])
      1 1 (one_mul 1) (by simp) (by simp)
  · exact selfDual_of_map volume inferInstance (fun t s => -1 * (t * s)) (fun x y => by ring)
      (ContinuousLinearEquiv.refl ℝ ℝ) Neg.neg (Homeomorph.neg ℝ).measurableEmbedding
      (fun x y => by simp [mul_comm]) 1 1 (one_mul 1) (by simp) (by simp)

theorem selfDual_dx {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (P Q : ℕ) :
    SelfDual (PerpendicularEmbedding.dx P Q) (fun x y : PerpendicularEmbedding.Sp P Q =>
      Complex.exp (2 * Real.pi * Complex.I *
        ((ε * (2 * (PerpendicularEmbedding.herm x y).re) : ℝ) : ℂ))) := by
  obtain ⟨u, hu1, hu2⟩ : ∃ u : Fin P ⊕ Fin Q → (ℂ ≃ₗᵢ[ℝ] ℂ),
      (∀ i z, u (Sum.inl i) z = ε * z) ∧ ∀ i z, u (Sum.inr i) z = -(ε * z) := by
    rcases hε with rfl | rfl
    · exact ⟨Sum.elim (fun _ => .refl ℝ ℂ) (fun _ => .neg ℝ), by simp, by simp⟩
    · exact ⟨Sum.elim (fun _ => .neg ℝ) (fun _ => .refl ℝ ℂ), by simp, by simp⟩
  let T : PerpendicularEmbedding.Sp P Q ≃L[ℝ] EuclideanSpace ℂ (Fin P ⊕ Fin Q) :=
    (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin P ⊕ Fin Q => ℂ).symm
  let S : EuclideanSpace ℂ (Fin P ⊕ Fin Q) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin P ⊕ Fin Q) :=
    LinearIsometryEquiv.piLpCongrRight 2 u
  have hT : MeasurePreserving T volume volume :=
    (show MeasurePreserving T.toHomeomorph.toMeasurableEquiv.symm volume volume from
      GlobalTheory.volume_preserving_ofLp_complex (Fin P ⊕ Fin Q)).symm _
  have hST : MeasurePreserving (S ∘ T) volume volume := S.measurePreserving.comp hT
  have h2 : MeasurableEmbedding fun w : EuclideanSpace ℂ (Fin P ⊕ Fin Q) => (2 : ℝ) • w :=
    (Homeomorph.smulOfNeZero (2 : ℝ) two_ne_zero).measurableEmbedding
  refine selfDual_of_map _ (GlobalTheory.RealPlaceCompare.isAddHaar_dx P Q)
    (fun x y => ε * (2 * (PerpendicularEmbedding.herm x y).re))
    (fun x y => by rw [← GlobalTheory.RealPlaceCompare.herm_star x y]; simp) T
    ((fun w => (2 : ℝ) • w) ∘ (S ∘ T))
    (h2.comp (S.toHomeomorph.measurableEmbedding.comp T.toHomeomorph.measurableEmbedding))
    (fun x y => ?_) (2 ^ (P + Q)) (2 ^ (P + Q))⁻¹ (mul_inv_cancel₀ (by positivity)) ?_ ?_
  · simp only [Function.comp, PiLp.inner_apply, Fintype.sum_sum_type,
      PerpendicularEmbedding.herm, Complex.sub_re, Complex.re_sum]
    have e : ∀ i, S (T y) i = u i (y i) := fun i => rfl
    have e' : ∀ i, T x i = x i := fun i => rfl
    simp only [e', Complex.inner, mul_sub, Finset.mul_sum]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> simp [e, hu1, hu2] <;> ring
  · rw [PerpendicularEmbedding.dx, Measure.map_smul, hT.map_eq]
    ext s hs
    simp [ENNReal.smul_def]
  · rw [← Measure.map_map h2.measurable hST.measurable, PerpendicularEmbedding.dx, Measure.map_smul, hST.map_eq,
      Measure.map_smul, Measure.map_addHaar_smul _ two_ne_zero,
      GlobalTheory.finrank_real_euclideanSpace_complex, smul_smul, ENNReal.smul_def]
    congr 1
    rw [abs_of_pos (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.coe_inv (by positivity)]
    simp only [Fintype.card_sum, Fintype.card_fin, ENNReal.ofReal_ofNat, ENNReal.coe_pow,
      ENNReal.coe_ofNat]
    generalize P + Q = n
    rw [two_mul, pow_add, ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
      ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

theorem selfDualReal : PerpendicularEmbedding.SelfDualReal := fun _ hε =>
  ⟨selfDual_dx hε, selfDual_line hε⟩

theorem realPlaceMeasures : ActionCoordinates.RealPlaceMeasures :=
  GlobalTheory.RealPlaceCompare.typings_agree.2.2.2.1
    ⟨selfDualReal, GlobalTheory.SphereMassProof.sphereMass, GlobalTheory.CompactDualQuot.compactDualQuotient⟩

end GlobalTheory.RealPlaceMeasuresProof
