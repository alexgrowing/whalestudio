import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometryOfNumbersLatticeEstimate
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.MomentBoundOfPointwiseMoments
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.AdmissibleFunctionClassClosureProperties
open UpperTheory.V.Lit.Geo

theorem UpperTheory.hermitian_space_geometric_estimate :
    MeanBd := by
  intro E _ _ _ a ha L hL
  obtain ⟨N, hN⟩ := UpperTheory.geometry_of_numbers_lattice_estimate E a ha L hL
  have hsum : ∀ g, Summable fun v : lat L g => gauss (pt (rt g) v.1) := by
    intro g
    have := ((hN g).2 1 1 one_pos le_rfl).1
    simpa only [one_mul, gauss] using this
  have h1 : ∀ g, 1 ≤ Th L g := by
    intro g
    have h := (hsum g).le_tsum (0 : lat L g) (fun j _ => (Real.exp_pos _).le)
    have h0 : gauss (pt (rt g) (0 : lat L g).1) = 1 := by
      simp [gauss, qf]
    rw [h0] at h
    exact h
  refine ⟨fun g => ⟨h1 g, ?_⟩, fun P hP => ?_⟩
  · simp only [Th, gsum, pg, Pi.one_apply, one_mul]
    exact (Complex.ofReal_tsum _).symm
  · obtain ⟨-, ⟨C, k, hC⟩, -⟩ := UpperTheory.admissibleFunctionClass_closure_properties E a P hP
    obtain ⟨D, hD0, hD⟩ := UpperTheory.moment_bound_of_pointwise_moments N k
    have hb : ∀ x, ‖pg P x‖ ≤ |C| * ((1 + qf x) ^ k * Real.exp (-Real.pi * qf x)) := by
      intro x
      have hq := qf_nonneg x
      have hg : 0 ≤ gauss x := (Real.exp_pos _).le
      rw [pg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hg, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ((hC x).trans ?_) hg
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    have hs : ∀ g, Summable fun v : lat L g => ‖pg P (pt (rt g) v.1)‖ := fun g =>
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun v => hb _)
        ((hD _ _ (hN g)).1.mul_left |C|)
    refine ⟨fun g => (hs g).of_norm, |C| * D, fun g => ?_⟩
    have hT : 0 < Th L g := lt_of_lt_of_le one_pos (h1 g)
    rw [mean, norm_div, Complex.norm_real, Real.norm_of_nonneg hT.le, div_le_iff₀ hT]
    calc ‖gsum L (pg P) g‖ ≤ ∑' v : lat L g, ‖pg P (pt (rt g) v.1)‖ := norm_tsum_le_tsum_norm (hs g)
      _ ≤ ∑' v : lat L g, |C| * ((1 + qf (pt (rt g) v.1)) ^ k * Real.exp (-Real.pi * qf (pt (rt g) v.1))) :=
        (hs g).tsum_le_tsum (fun v => hb _) ((hD _ _ (hN g)).1.mul_left |C|)
      _ = |C| * ∑' v : lat L g, ((1 + qf (pt (rt g) v.1)) ^ k * Real.exp (-Real.pi * qf (pt (rt g) v.1))) :=
        tsum_mul_left
      _ ≤ |C| * (D * Th L g) := mul_le_mul_of_nonneg_left (hD _ _ (hN g)).2 (abs_nonneg _)
      _ = |C| * D * Th L g := (mul_assoc _ _ _).symm
