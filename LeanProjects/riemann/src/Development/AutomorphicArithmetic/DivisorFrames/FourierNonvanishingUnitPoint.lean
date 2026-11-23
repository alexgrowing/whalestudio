import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBDefs
open MeasureTheory FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB

private theorem exists_rep {ι : Type} [Fintype ι] (l : (ι → ℂ) →ₗ[ℝ] ℝ) :
    ∃ y : ι → ℂ, ∀ s : ι → ℂ, l s = (∑ w, (s * y) w).re := by
  classical
  refine ⟨fun w => (l (Pi.single w 1) : ℂ) - (l (Pi.single w Complex.I) : ℂ) * Complex.I, fun s => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single s]
  rw [map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : (Pi.single w (s w) : ι → ℂ) =
      (s w).re • (Pi.single w 1 : ι → ℂ) + (s w).im • (Pi.single w Complex.I : ι → ℂ) := by
    rw [← Pi.single_smul, ← Pi.single_smul, ← Pi.single_add]
    congr 1
    simp
  rw [h, map_add, map_smul, map_smul]
  simp

private theorem continuous_FT {ι : Type} [Fintype ι] (φ : (ι → ℂ) → ℂ) (hc : Continuous φ)
    (hi : Integrable φ) : Continuous (FT φ) := by
  unfold FT
  refine continuous_of_dominated (bound := fun s => ‖φ s‖) (fun y => ?_) (fun y => ?_) hi.norm ?_
  · exact (hc.mul (continuous_ec.comp (continuous_id.mul continuous_const))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun s => by rw [norm_mul, norm_ec, mul_one]
  · exact Filter.Eventually.of_forall fun s =>
      continuous_const.mul (continuous_ec.comp (continuous_const.mul continuous_id))

open FourierTransform in
theorem UpperTheory.fourier_nonvanishing_unit_point :
    ∀ {ι : Type} [Fintype ι] (φ : (ι → ℂ) → ℂ), Continuous φ → Integrable φ → φ ≠ 0 →
        ∃ y : ι → ℂ, (∀ w, y w ≠ 0) ∧ FT φ y ≠ 0 := by
  intro ι _ φ hc hi hne
  by_contra hcon
  push Not at hcon
  have h0 : FT φ = fun _ => 0 :=
    Continuous.ext_on dense_ne_zero (continuous_FT φ hc hi) continuous_const fun y hy => hcon y hy
  let T : EuclideanSpace ℝ (Fin (Module.finrank ℝ (ι → ℂ))) ≃L[ℝ] (ι → ℂ) := toEuclidean.symm
  haveI : (Measure.map T volume).IsAddHaarMeasure := T.isAddHaarMeasure_map _
  have hm := Measure.isAddLeftInvariant_eq_smul (Measure.map T volume) (volume : Measure (ι → ℂ))
  set c := Measure.addHaarScalarFactor (Measure.map T volume) (volume : Measure (ι → ℂ))
  have hme : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  have hfi : Integrable (φ ∘ T) := by
    rw [← hme.integrable_map_iff, hm]
    exact hi.smul_measure_nnreal
  have hF : 𝓕 (φ ∘ T) = fun _ => 0 := by
    funext w
    obtain ⟨y, hy⟩ := exists_rep (((innerₗ _).flip w) ∘ₗ (T.symm : (ι → ℂ) →ₗ[ℝ] _))
    have h1 : ∫ s, φ s * ec (s * y) ∂(Measure.map T volume) = 0 := by
      rw [hm, integral_smul_nnreal_measure]
      have := congrFun h0 y
      unfold FT at this
      rw [this, smul_zero]
    rw [hme.integral_map] at h1
    rw [Real.fourier_eq', ← h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    have h2 := hy (T v)
    simp only [ec, ← h2]
    simp [mul_comm]
    left
    rw [real_inner_comm]
    congr 1
    ring
  have hinv := (hc.comp T.continuous).fourierInv_fourier_eq hfi (by rw [hF]; exact integrable_zero _ _ _)
  apply hne
  funext s
  have := congrFun hinv (T.symm s)
  rw [hF, Real.fourierInv_eq] at this
  simpa using this.symm
