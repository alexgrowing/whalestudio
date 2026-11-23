import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PoinSumMul
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.UnfoldPoincareOnto
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SingularMetricFreeDivisorInvariantLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SingularMetricFreeDivisorSmoothCurvatureStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SquareIntegrableSingularMetricOrderOneStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.OneDivisionUpstairsFreeWeightStatement

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.DivFreeWeight

open ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra GlobalTheory.Up.DivCorePf

theorem division_order_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r), (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m ∧ ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, m * leviRh X x0 z ξ ≤ leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ) → (∀ P, X.IsBddSec (G + (nd X + 1) • Xa.L) P → P ∈ X.SS (G + (nd X + 1) • Xa.L)) → (∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS (G + (nd X + 1) • Xa.L), ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f x = ∑ i, c i * g i x) → ∀ f, X.IsBddSec (G + (nd X + 1) • Xa.L) f → (∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm (G + (nd X + 1) • Xa.L) f x ^ 2 ≤ C * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (nd X + 1)) → (∀ j, f (Fl.xs j) = 0) → ∃ h : Fin (nd X) → Frame X.Ψ r → ℂ, (∀ k, X.IsBddSec (G + nd X • Xa.L) (h k)) ∧ ∀ x ∈ X.dom, f x = ∑ k, Fl.s k x * h k x := by
  intro E _ _ _ r X Xa Fl G ⟨bb, m, hbb, hbm, hmar⟩ hcusp ⟨K, gs, hgs⟩ f hf hfC hvan
  have h2 := Xa.n_ge
  have hPD : PropDisc X := GlobalTheory.ClosedDiscontinuity.propDisc_closed r X
  obtain ⟨-, -, -, hPo, hOn⟩ := GlobalTheory.PoincareClosed.unfold_poincare_onto (E := E)
  have hExt := GlobalTheory.FrameMeasureClosed.extF_holds (E := E)
  obtain ⟨x0, ho⟩ : ∃ x0, IsOrth X x0 := by
    choose P hP hG using X.signature
    exact ⟨fun τ => P τ, fun τ => hG τ⟩
  obtain ⟨FF, hFF⟩ := fundSet_holds r X x0 ho hPD
  have hbb0 : 0 ≤ bb := le_trans (by positivity) hbb.le
  have hbm' : bb ≤ m := by
    have : 0 ≤ bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) := by positivity
    linarith
  have hs : ∀ k, X.IsSec Xa.L (Fl.s k) := fun k => (Fl.s_van k).1.1.1
  have hIn := GlobalTheory.T.square_integrable_singular_metric_order_one E r X Xa Fl G x0 ho FF hFF f hf.1 hfC hvan
  obtain ⟨hMT, hLT, hET⟩ := GlobalTheory.T.singularMetricFreeDivisor_invariant_lower_bound E r X Xa Fl G (nd X + 1) (by omega)
  obtain ⟨hMn, hLn, -⟩ := GlobalTheory.T.singularMetricFreeDivisor_invariant_lower_bound E r X Xa Fl G (nd X) (by omega)
  obtain ⟨⟨k0, z0, hz0, hz0'⟩, hLev⟩ := GlobalTheory.T.singularMetricFreeDivisor_smooth_curvature E r X Xa Fl G (nd X + 1) (by omega) x0 ho
  obtain ⟨F, P, hF, hFI, hP, hPF, hpo⟩ := hOn r X x0 ho hPD _ _
    (fun x => phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) +
      (((nd X + 1 : ℕ) : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2))
    (fun z => Fl.s k0 (cpt X x0 z)) bb m hMT hLT hbb hbm (OntoB.hol_comp X x0 (hs k0).1)
    ⟨z0, hz0, hz0'⟩ (hLev k0).1 (fun z hz hz' => hET _ hz ⟨k0, hz'⟩)
    (fun z hz hz' ξ => (hmar x0 ho z hz ξ).trans ((hLev k0).2 z hz hz' ξ)) hcusp FF hFF
    ⟨K, gs, fun f hf _ => hgs f hf⟩ _ (hcusp _ hf) hIn
  obtain ⟨H, hH, hFH⟩ := GlobalTheory.T.one_division_upstairs_free_weight E r X Xa Fl G x0 ho bb
    (fun z hz ξ => (mul_le_mul_of_nonneg_right hbm'
      (OntoB.levi_rh_nonneg RhGradFStatement_holds ho hz ξ)).trans (hmar x0 ho z hz ξ))
    ⟨k0, z0, hz0, hz0'⟩ F hF hFI
  choose Q hQ hQH using fun k => exists_extension hExt ho hLn hbb0 (hH k).1 (hH k).2
  have hPQ := fun k => hPo r X x0 ho hPD _ _ bb hMn hLn hbb (H k) (Q k) (hH k).1 (hH k).2 (hQ k) (hQH k)
  have hwt : G + (nd X + 1) • Xa.L = G + nd X • Xa.L + Xa.L := by
    rw [succ_nsmul, add_assoc]
  have hsum : ∀ y ∈ X.dom, P y = ∑ k, Fl.s k y * Q k y := by
    intro y hy
    refine sub_eq_zero.1 (bigCellStatement_holds r X x0 ho (G + (nd X + 1) • Xa.L)
      (fun y => P y - ∑ k, Fl.s k y * Q k y) ⟨?_, fun x hx b hb => ?_⟩ (fun z hz => ?_) y hy)
    · exact hP.1.sub (DifferentiableOn.fun_sum fun k _ => (hs k).1.mul (hQ k).1)
    · beta_reduce
      rw [mul_sub, hP.2 x hx b hb, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [(hs k).2.1 x hx b hb, (hQ k).2 x hx b hb, hwt, bchar_add X hb _ Xa.L]
      ring
    · rw [hPF z hz, hFH z hz, sub_eq_zero]
      exact Finset.sum_congr rfl fun k _ => by rw [hQH k z hz]
  refine ⟨fun k => poin X (G + nd X • Xa.L) (Q k), fun k => (hPQ k).2.1, fun x hx => ?_⟩
  rw [← hpo x hx, hwt]
  exact poin_sum_mul _ (fun k _ => hs k) hsum hx fun k _ => (hPQ k).1 x hx

end GlobalTheory.DivFreeWeight
