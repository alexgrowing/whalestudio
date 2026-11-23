import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SumNormSqOrbit
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaFormsBoundedByGenericCombinationsStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaFormsNotSmallWhereCombinationsVanishStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AeCoefficientsCommonZerosSimpleStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AeTranscendentalPointNonvanishingStatement

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.GenericFlat

theorem ae_exists_flat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (K : Type) [Field K] [Countable K] (σ : K →+* ℂ), RelIn σ X Xa → ∀ᵐ t : Fin (nd X + 1) × Fin Xa.N → ℂ, ∃ Fl : FlatM X Xa, (∀ x, Fl.w0 x = ∑ j, t (0, j) * Xa.w j x) ∧ ∀ k x, Fl.s k x = ∑ j, t (k.succ, j) * Xa.w j x := by
  intro E _ _ _ r X Xa K _ _ σ hR
  filter_upwards [GlobalTheory.T.ae_transcendental_point_nonvanishing K σ (Fin (nd X + 1) × Fin Xa.N), GlobalTheory.T.ae_coefficients_common_zeros_simple E r X Xa] with t hgen hsimple

  have hdom : ∃ C : ℝ, ∀ x ∈ X.dom, ∑ k, ‖Xa.w k x‖ ^ 2 ≤ C * ∑ i, ‖∑ j, t (i, j) * Xa.w j x‖ ^ 2 :=
    GlobalTheory.T.theta_forms_bounded_by_generic_combinations E r X Xa K σ t hgen hR
  have hlow : ∃ ε c0 : ℝ, 0 < ε ∧ 0 < c0 ∧ ∀ x ∈ X.dom,
      ∑ i : Fin (nd X), ‖∑ j, t (i.succ, j) * Xa.w j x‖ ^ 2 < ε * ‖∑ j, t (0, j) * Xa.w j x‖ ^ 2 →
        c0 ≤ ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 :=
    GlobalTheory.T.theta_forms_not_small_where_combinations_vanish E r X Xa K σ t hgen hR
  have hsim : ∀ x ∈ X.dom, ∑ j, t (0, j) * Xa.w j x ≠ 0 →
      (∀ k : Fin (nd X), ∑ j, t (k.succ, j) * Xa.w j x = 0) →
      (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
        (∑ j, t (k.succ, j) * Xa.w j (cpt X x z)) / ∑ j, t (0, j) * Xa.w j (cpt X x z) : V (nd X))) 0).det ≠ 0 :=
    hsimple
  obtain ⟨C, hC⟩ := hdom

  have hzero : ∀ x ∈ X.dom, (∀ k : Fin (nd X), ∑ j, t (k.succ, j) * Xa.w j x = 0) →
      (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
        (∑ j, t (k.succ, j) * Xa.w j (cpt X x z)) / ∑ j, t (0, j) * Xa.w j (cpt X x z) : V (nd X))) 0).det ≠ 0 := by
    intro x hx hs
    have hs0 : ∑ j, t (0, j) * Xa.w j x ≠ 0 := by
      intro h0
      obtain ⟨k, hk⟩ := Xa.w_nz x hx
      have hsum : ∑ i, ‖∑ j, t (i, j) * Xa.w j x‖ ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨m, rfl⟩
        · simp [h0]
        · simp [hs m]
      have hle := hC x hx
      rw [hsum, mul_zero] at hle
      have hk' : ‖Xa.w k x‖ ^ 2 ≤ ∑ k, ‖Xa.w k x‖ ^ 2 :=
        Finset.single_le_sum (f := fun k => ‖Xa.w k x‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)
      have h2 : ‖Xa.w k x‖ ^ 2 = 0 := le_antisymm (hk'.trans hle) (by positivity)
      exact hk (by simpa using h2)
    exact hsim x hx hs0 hs
  obtain ⟨Fl, h0, hs⟩ := GlobalTheory.FlatPoints.exists_flat GlobalTheory.ClosedDiscontinuity.firstMinimum_invariant_continuous_pos_on_frames
    GlobalTheory.FlagMahler.mahler_compactness r X Xa (fun i j => t (i, j)) ⟨C, hC⟩ hlow hzero
  exact ⟨Fl, fun x => congrFun h0 x, fun k x => congrFun (congrFun hs k) x⟩

end GlobalTheory.GenericFlat
