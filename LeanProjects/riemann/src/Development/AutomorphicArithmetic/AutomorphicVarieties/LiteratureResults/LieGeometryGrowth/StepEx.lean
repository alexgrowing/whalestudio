import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.UnitaryGroupLieAlgebraEqSkewHermitian
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.UnitarySimilitudeGroupIsSmoothCmDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.LatticePointCountBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianGaussianMomentBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceGeometricEstimate
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.LieDerivativeIsDerivationSmoothFunctions
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.RealLieGroupChartsSmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianTraceFormEstimate
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianTraceFormEntryEstimate
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceLogEstimate
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpacePointLogEstimate
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.TraceFormPosDefOfTotallyReal

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo

private theorem trF_smul {E : Type} [Field E] [NumberField E] {a : ℕ} (s : ℝ) (X Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    trF X (s • Y) = s * trF X Y := by
  simp [trF, Finset.mul_sum]

theorem UpperTheory.V.Lit.Geo.stepEx :
    StepEx := by
  intro E _ _ _ a ha U hU
  obtain ⟨L, hL, hUL⟩ := UpperTheory.unitaryGroup_lieAlgebra_eq_skewHermitian E a U hU
  obtain ⟨ε₁, C₁, hε₁, hroot⟩ := UpperTheory.unitarySimilitudeGroup_isSmooth_cmDatum E a
  obtain ⟨hI1, hI2, hI3⟩ := UpperTheory.lattice_point_count_bound E a ha L
  have hK := UpperTheory.hermitian_gaussian_moment_bound E a ha L hL
  obtain ⟨hT, hM⟩ := UpperTheory.hermitian_space_geometric_estimate E a ha L hL
  obtain ⟨hS1, φ, hφ, hS2⟩ := UpperTheory.realLieGroup_charts_smooth E a ha L hL
  obtain ⟨hB1, hB2⟩ := UpperTheory.lieDerivative_isDerivation_smoothFunctions E a {f | ∃ P ∈ poly E a, f = mean L P} (by
    rintro _ ⟨P, hP, rfl⟩
    exact ⟨(hM P hP).2, hS1 P hP⟩)
  obtain ⟨hD1, ⟨B, hB, hD2⟩, hD3⟩ := UpperTheory.hermitian_trace_form_estimate E a ha L hL
  obtain ⟨C₂, ε₂, hC₂, hε₂, hTay⟩ := UpperTheory.hermitian_trace_form_entry_estimate E a ha L hL
  obtain ⟨C₃, hC₃⟩ := UpperTheory.hermitian_space_log_estimate E a ha L hL
  obtain ⟨C₄, hC₄⟩ := UpperTheory.hermitian_space_point_log_estimate E a ha L hL
  obtain ⟨c₀, f₀, hc₀, hG⟩ := UpperTheory.traceForm_posDef_of_totallyReal E a ha L hL
  obtain ⟨δ, hδ, hδ1, hδ2, hδ3⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * B ≤ ε₁ ∧ δ * B ≤ ε₂ ∧ C₂ * (δ * B) ^ 2 ≤ δ * c₀ := by
    have hp : 0 < C₂ * B ^ 2 + 1 := by positivity
    refine ⟨min (min (ε₁ / B) (ε₂ / B)) (c₀ / (C₂ * B ^ 2 + 1)), by positivity, ?_, ?_, ?_⟩
    · exact (le_div_iff₀ hB).1 ((min_le_left _ _).trans (min_le_left _ _))
    · exact (le_div_iff₀ hB).1 ((min_le_left _ _).trans (min_le_right _ _))
    · set d := min (min (ε₁ / B) (ε₂ / B)) (c₀ / (C₂ * B ^ 2 + 1))
      have h0 : 0 < d := by positivity
      have h1 : d * (C₂ * B ^ 2 + 1) ≤ c₀ := (le_div_iff₀ hp).1 (min_le_right _ _)
      nlinarith
  have hf0 : ∀ g, 0 ≤ fn L g := fun g => Real.log_nonneg (hT g).1
  have hq0 : ∀ g : GA E a, 0 ≤ Real.log (qht g) := fun g => Real.log_nonneg
    (le_ciInf fun _ => GroundTheory.Automorphic.AutomorphicForm.one_le_height _)
  have hn : ∀ g (t : ℝ), |t| ≤ 1 → ‖toL (t • ((-δ) • dev L g).1)‖ ≤ δ * B := fun g t ht => by
    change ‖t • (-δ) • toL (dev L g).1‖ ≤ _
    rw [norm_smul, norm_smul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hδ]
    have h1 := mul_le_mul_of_nonneg_left (hD2 g).2.1 hδ.le
    have h2 : 0 ≤ δ * ‖toL (dev L g).1‖ := by positivity
    nlinarith
  have key : ∀ g (t : ℝ) (h : GL (Fin a) (Cinf E)), |t| ≤ 1 → h.val * star h.val = 1 + t • ((-δ) • dev L g).1 →
      |fn L (g * infGL E a h) - fn L g - Real.pi * t * δ * trF (dev L g).1 (dev L g).1| ≤ δ * c₀ := fun g t h ht hh => by
    have h0 : ell E a (toL (t • ((-δ) • dev L g).1)) = 0 := by
      change ell E a (t • (-δ) • toL (dev L g).1) = 0
      rw [map_smul, map_smul, (hD3 g).1, smul_zero, smul_zero]
    have h1 := hTay g _ h h0 ((hn g t ht).trans hδ2) hh
    have h2 : trF (mom L g).1 (t • ((-δ) • dev L g).1) = -(t * δ * trF (dev L g).1 (dev L g).1) := by
      change trF (mom L g).1 (t • (-δ) • (dev L g).1) = _
      rw [trF_smul, trF_smul, (hD3 g).2]
      ring
    rw [h2] at h1
    have h3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hn g t ht) 2) hC₂
    refine le_trans (le_of_eq ?_) (h1.trans (h3.trans hδ3))
    congr 1
    ring
  have hπ : 0 ≤ Real.pi - 2 := by linarith [Real.pi_gt_three]
  refine ⟨fn L, fun g => (-δ) • dev L g, max (max C₁ (Real.pi * δ * B + δ * c₀)) (max C₃ C₄), δ * c₀, f₀,
    ⟨mul_pos hδ hc₀, ⟨φ, hφ, hB2 φ hS2⟩, fun γ t g => (hI1 γ t g).1, fun k g => ?_, fun u hu g => (hI2 U hU hUL u hu g).1,
      hf0, fun g => ?_, fun g => ?_, fun i j w => ?_, fun γ t g => ?_, fun k g => ?_, fun u hu g => ?_, fun g t ht => ?_,
      fun g h hg hh => ?_, fun g h hg hh => ?_, fun g t h ht hh => ?_⟩⟩
  · rw [fn, hI3, fn]
  · exact (hC₃ g).trans (mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_left _ _)) (by linarith [hq0 g]))
  · exact (hC₄ g).trans (mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_right _ _)) (by linarith [hf0 g]))
  · obtain ⟨ψ, h1, h2⟩ := hB1 _ (Subalgebra.smul_mem _ (hD1 i j w) ((-δ : ℝ) : ℂ))
    exact ⟨ψ, fun g => by rw [h1]; rfl, h2⟩
  · rw [(hI1 γ t g).2]
  · rw [← hK k g]
    exact Subtype.ext (by simp [adHerm])
  · rw [(hI2 U hU hUL u hu g).2]
  · obtain ⟨h, h1, h2, h3⟩ := hroot (t • (-δ) • dev L g) ((hn g t ht).trans hδ1)
    exact ⟨h, h1, h2.trans (le_max_of_le_left (le_max_left _ _)), h3.trans (le_max_of_le_left (le_max_left _ _))⟩
  · have h1 := (abs_le.1 (key g 1 h (by simp) (by rwa [one_smul]))).1
    have h2 := mul_le_mul_of_nonneg_left (hG g hg) hδ.le
    have h3 := mul_pos hδ hc₀
    nlinarith
  · have h1 := (abs_le.1 (key g (-1) h (by simp) (by rwa [neg_one_smul, ← sub_eq_add_neg]))).2
    have h2 := mul_le_mul_of_nonneg_left (hG g hg) hδ.le
    have h3 := mul_pos hδ hc₀
    nlinarith
  · refine le_max_of_le_left (le_max_of_le_right ?_)
    have h1 := key g t h ht hh
    have h2 : |Real.pi * t * δ * trF (dev L g).1 (dev L g).1| ≤ Real.pi * δ * B := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hδ]
      have := (hD2 g).2.2
      calc Real.pi * |t| * δ * |trF (dev L g).1 (dev L g).1| ≤ Real.pi * 1 * δ * B := by
            have := Real.pi_pos
            gcongr
        _ = _ := by ring
    have h3 := abs_add_le (fn L (g * infGL E a h) - fn L g - Real.pi * t * δ * trF (dev L g).1 (dev L g).1)
      (Real.pi * t * δ * trF (dev L g).1 (dev L g).1)
    rw [sub_add_cancel] at h3
    linarith
