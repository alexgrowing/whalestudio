import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeas
open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ConeHaar

variable {n : ℕ}

theorem posDef_congr_iff (g H : Mat n) (hg : g.det ≠ 0) : (g * H * gᴴ).PosDef ↔ H.PosDef := by
  have hU : IsUnit (star g) := ((Matrix.isUnit_iff_isUnit_det g).2 (isUnit_iff_ne_zero.2 hg)).star
  have h := Matrix.IsUnit.posDef_star_left_conjugate_iff (x := H) hU
  rwa [star_star, Matrix.star_eq_conjTranspose] at h

theorem det_congr_re (g H : Mat n) : (g * H * gᴴ).det.re = ‖g.det‖ ^ 2 * H.det.re := by
  have h1 : (g * H * gᴴ).det = ((‖g.det‖ ^ 2 : ℝ) : ℂ) * H.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def,
      ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    ring
  rw [h1, Complex.re_ofReal_mul]

theorem coneW_congr (g : Mat n) (v w : Fin n × Fin n → ℝ) (h : hOf w = g * hOf v * gᴴ) :
    coneW n w = ENNReal.ofReal ((‖g.det‖ ^ (2 * n))⁻¹) * coneW n v := by
  unfold coneW
  rw [h, det_congr_re, ← ENNReal.ofReal_mul (inv_nonneg.2 (pow_nonneg (norm_nonneg g.det) (2 * n))),
    mul_pow, ← pow_mul, mul_inv]

theorem map_coneMeas_eq (n : ℕ) (g : Mat n) (hg : g.det ≠ 0)
    (T : (Fin n × Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ)) (hT : ∀ v, hOf (T v) = g * hOf v * gᴴ)
    (hdet : LinearMap.det T = ‖g.det‖ ^ (2 * n)) : Measure.map T (coneMeas n) = coneMeas n := by
  have hd : 0 < LinearMap.det T := by
    rw [hdet]
    exact pow_pos (norm_pos_iff.2 hg) _
  have hdT : LinearMap.det T ≠ 0 := hd.ne'
  let e : (Fin n × Fin n → ℝ) ≃ᵐ (Fin n × Fin n → ℝ) :=
    (LinearMap.equivOfDetNeZero T hdT).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : (e : (Fin n × Fin n → ℝ) → (Fin n × Fin n → ℝ)) = T := rfl
  have hC : e ⁻¹' cone n = cone n := by
    ext v
    show (hOf (T v)).PosDef ↔ (hOf v).PosDef
    rw [hT v]
    exact posDef_congr_iff g (hOf v) hg
  have hW : ∀ v, coneW n (e v) = ENNReal.ofReal (LinearMap.det T)⁻¹ * coneW n v := by
    intro v
    rw [hdet]
    exact coneW_congr g v (T v) (hT v)
  have hvol : Measure.map e volume
      = ENNReal.ofReal (LinearMap.det T)⁻¹ • (volume : Measure (Fin n × Fin n → ℝ)) := by
    rw [he, Real.map_linearMap_volume_pi_eq_smul_volume_pi hdT, abs_of_pos (inv_pos.2 hd)]
  have hmap : Measure.map e ((volume : Measure (Fin n × Fin n → ℝ)).restrict (cone n))
      = ENNReal.ofReal (LinearMap.det T)⁻¹ •
        (volume : Measure (Fin n × Fin n → ℝ)).restrict (cone n) := by
    conv_lhs => rw [← hC]
    rw [← MeasurableEquiv.restrict_map, hvol, Measure.restrict_smul]
  have ha0 : ENNReal.ofReal (LinearMap.det T)⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hd)).ne'
  have hatop : ENNReal.ofReal (LinearMap.det T)⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← he]
  ext s hs
  rw [MeasurableEquiv.map_apply]
  unfold coneMeas
  rw [withDensity_apply _ (e.measurable hs), withDensity_apply _ hs,
    ← ENNReal.mul_right_inj ha0 hatop]
  calc ENNReal.ofReal (LinearMap.det T)⁻¹ *
        ∫⁻ v in e ⁻¹' s, coneW n v ∂(volume : Measure (Fin n × Fin n → ℝ)).restrict (cone n)
      = ∫⁻ v in e ⁻¹' s, coneW n (e v) ∂(volume : Measure (Fin n × Fin n → ℝ)).restrict (cone n) := by
        simp_rw [hW]
        rw [lintegral_const_mul' _ _ hatop]
    _ = ∫⁻ w in s, coneW n w
          ∂Measure.map e ((volume : Measure (Fin n × Fin n → ℝ)).restrict (cone n)) := by
        rw [MeasurableEquiv.restrict_map, lintegral_map_equiv]
    _ = ENNReal.ofReal (LinearMap.det T)⁻¹ *
          ∫⁻ w in s, coneW n w ∂(volume : Measure (Fin n × Fin n → ℝ)).restrict (cone n) := by
        rw [hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]

end GlobalTheory.CompanionTheory.ConeHaar
