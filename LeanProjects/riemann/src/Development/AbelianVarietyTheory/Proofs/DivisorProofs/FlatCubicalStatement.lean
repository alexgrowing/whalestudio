import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodTorusFlatCoordsInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodFlatMapRealAnalyticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapSymplecticTransformStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatCoordsSymplecticPullbackFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormSmoothOnCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormClosedOnCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormTypeOneOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormVerticalNegativeImagPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormMulPullZeroSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormWedgePowerVanishesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormFibreIntegralEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationPreservesFlatFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormKernelHorizontalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMetricChernFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricDeterminedByCurvatureZeroSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalMetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareIsomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIsoIsometryCubicalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapRigidityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPeriodMapSimplyConnectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelActionIsMulActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelActionPreservesFlatFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSymplecticPreservesOrbitsStatement

open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.FlatCubicalProof

theorem flatCubical : FlatCubical := by
  intro g
  refine ⟨fun E _ _ _ B τ hτ => ⟨?_, ?_, GlobalTheory.T.period_map_rigidity hτ⟩, ?_⟩
  · exact ⟨GlobalTheory.T.period_torus_flat_coords_inverse hτ, (GlobalTheory.T.period_flat_map_real_analytic hτ).1, (GlobalTheory.T.period_flat_map_real_analytic hτ).2, fun γ => ⟨(GlobalTheory.T.period_map_symplectic_transform hτ γ).1,
      (GlobalTheory.T.period_map_symplectic_transform hτ γ).2.1, (GlobalTheory.T.period_map_symplectic_transform hτ γ).2.2, fun P hP => GlobalTheory.T.flat_coords_symplectic_pullback_form hτ γ P hP⟩,
      GlobalTheory.T.flat_form_smooth_on_cover hτ, GlobalTheory.T.flat_form_closed_on_cover hτ, GlobalTheory.T.flat_form_type_one_one hτ, (GlobalTheory.T.flat_form_vertical_negative_imag_positive hτ).1, (GlobalTheory.T.flat_form_vertical_negative_imag_positive hτ).2, (GlobalTheory.T.flat_form_mul_pull_zero_section hτ).1,
      (GlobalTheory.T.flat_form_mul_pull_zero_section hτ).2, GlobalTheory.T.flat_form_wedge_power_vanishes hτ, GlobalTheory.T.flat_form_fibre_integral_eq_one hτ, GlobalTheory.T.translation_preserves_flat_form hτ, (GlobalTheory.T.flat_form_kernel_horizontal hτ).1, (GlobalTheory.T.flat_form_kernel_horizontal hτ).2⟩
  · intro j r hj hs hr hp
    refine ⟨GlobalTheory.T.exists_cubical_metric hτ j r hj hs hr hp, fun h h' hh hh' => ?_, fun n =>
      ⟨GlobalTheory.T.exists_square_isomorphism hτ j r hj hs hr hp n, fun h φ hh hφ => GlobalTheory.T.square_iso_isometry_cubical hτ j r hj hs hr hp n h φ hh hφ⟩⟩
    refine GlobalTheory.T.metric_determined_by_curvature_zero_section hτ j h h' hh.1 hh'.1 (fun P hP v w => ?_) (fun b hb => ?_)
    · have e1 := hh.2.1 P hP v w
      have e2 := hh'.2.1 P hP v w
      linarith
    · have e1 := hh.2.2 b hb
      have e2 := hh'.2.2 b hb
      have hne : ‖r b‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 (hr.2 b hb))
      exact mul_right_cancel₀ hne (e1.trans e2.symm)
  · refine ⟨(GlobalTheory.T.siegel_period_map_simply_connected g).1, (GlobalTheory.T.siegel_period_map_simply_connected g).2, (GlobalTheory.T.siegel_action_is_mul_action g).1, (GlobalTheory.T.siegel_action_is_mul_action g).2, fun γ =>
      ⟨(GlobalTheory.T.siegel_action_preserves_flat_form g γ).1, (GlobalTheory.T.siegel_action_preserves_flat_form g γ).2.1, (GlobalTheory.T.siegel_action_preserves_flat_form g γ).2.2, GlobalTheory.T.rational_symplectic_preserves_orbits g γ⟩, ?_⟩
    exact ⟨_, _, (theta_factor (GlobalTheory.T.siegel_period_map_simply_connected g).1).1, (GlobalTheory.T.theta_metric_chern_flat (GlobalTheory.T.siegel_period_map_simply_connected g).1).1,
      (GlobalTheory.T.theta_metric_chern_flat (GlobalTheory.T.siegel_period_map_simply_connected g).1).2⟩

end GlobalTheory.FlatCubicalProof
