import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Dchart
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellDens.ScaledVol

theorem measurePreserving_inv_sqrt_two_smul (r : ℕ) :
    MeasurePreserving (fun y : Fin r → ℂ => (√2 : ℝ)⁻¹ • y) volume
      (((2 : ℝ≥0∞) ^ r) • volume) := by
  have hs : (√2 : ℝ)⁻¹ ≠ 0 := by positivity
  have hfin : Module.finrank ℝ (Fin r → ℂ) = 2 * r := by
    rw [Module.finrank_pi_fintype]; simp [Complex.finrank_real_complex]; ring
  refine ⟨by fun_prop, ?_⟩
  rw [Measure.map_addHaar_smul _ hs, hfin, inv_pow, inv_inv, pow_mul, Real.sq_sqrt (by norm_num),
    abs_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
  simp

theorem volume_image_eq (A B F : Type) [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [FiniteDimensional ℝ A] [MeasurableSpace A] [BorelSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℝ B] [FiniteDimensional ℝ B] [MeasurableSpace B] [BorelSpace B]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
    [BorelSpace F] (r : ℕ) (L : ((A × A) × ((Fin r → ℂ) × B)) ≃L[ℝ] F)
    (hL : ∀ v, ‖L v‖ ^ 2 =
      ‖v.1.1‖ ^ 2 + ‖v.1.2‖ ^ 2 + 2 * (∑ a, ‖v.2.1 a‖ ^ 2) + ‖v.2.2‖ ^ 2)
    (s : Set ((A × A) × ((Fin r → ℂ) × B))) (hs : MeasurableSet s) :
    volume (L '' s) = 2 ^ r * volume s := by
  have hc : (√2 : ℝ)⁻¹ ≠ 0 := by positivity
  let Ψ : WithLp 2 (WithLp 2 (A × A) × WithLp 2 (EuclideanSpace ℂ (Fin r) × B)) ≃ₗ[ℝ]
      ((A × A) × ((Fin r → ℂ) × B)) :=
    (WithLp.linearEquiv 2 ℝ _).trans
      (LinearEquiv.prodCongr (WithLp.linearEquiv 2 ℝ (A × A))
        ((WithLp.linearEquiv 2 ℝ _).trans
          (LinearEquiv.prodCongr
            ((WithLp.linearEquiv 2 ℝ (Fin r → ℂ)).trans
              (LinearEquiv.smulOfNeZero ℝ (Fin r → ℂ) (√2 : ℝ)⁻¹ hc))
            (LinearEquiv.refl ℝ B))))
  have hΨ : ∀ x, Ψ x = (x.ofLp.1.ofLp, ((√2 : ℝ)⁻¹ • x.ofLp.2.ofLp.1.ofLp, x.ofLp.2.ofLp.2)) :=
    fun _ => rfl
  let G : WithLp 2 (WithLp 2 (A × A) × WithLp 2 (EuclideanSpace ℂ (Fin r) × B)) ≃ₗᵢ[ℝ] F :=
    { Ψ.trans L.toLinearEquiv with
      norm_map' := fun x => by
        change ‖L (Ψ x)‖ = ‖x‖
        rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), hL, hΨ, WithLp.prod_norm_sq_eq_of_L2,
          WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq]
        simp [norm_smul, mul_pow, Finset.mul_sum, ← mul_assoc, add_assoc] }
  have h0 := (measurePreserving_inv_sqrt_two_smul r).comp
    (GlobalTheory.volume_preserving_ofLp_complex (Fin r))
  haveI : SFinite (((2 : ℝ≥0∞) ^ r) • (volume : Measure (Fin r → ℂ))) := inferInstance
  have h1 := (h0.prod (MeasurePreserving.id (volume : Measure B))).comp
    (WithLp.volume_preserving_ofLp (EuclideanSpace ℂ (Fin r)) B)
  have h2 := ((WithLp.volume_preserving_ofLp A A).prod h1).comp
    (WithLp.volume_preserving_ofLp (WithLp 2 (A × A)) (WithLp 2 (EuclideanSpace ℂ (Fin r) × B)))
  have h3 := h2.measure_preimage hs.nullMeasurableSet
  rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.smul_apply, smul_eq_mul,
    ← Measure.volume_eq_prod, ← Measure.volume_eq_prod] at h3
  have hm : MeasurableSet (L '' s) :=
    L.toHomeomorph.toMeasurableEquiv.measurableEmbedding.measurableSet_image.2 hs
  rw [← h3, ← G.measurePreserving.measure_preimage hm.nullMeasurableSet]
  congr 1
  ext x
  change L (Ψ x) ∈ L '' s ↔ Ψ x ∈ s
  exact L.injective.mem_set_image

end GlobalTheory.CellDens.ScaledVol
