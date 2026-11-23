import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogRatioLowerBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.PlugPairs
import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ConstantSupremum.SupremumConstantLogBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogRatioLowerBoundStatement

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
namespace GlobalTheory.CovTop.MeasLow
end GlobalTheory.CovTop.MeasLow
namespace GlobalTheory.CovTop.MeasLow
end GlobalTheory.CovTop.MeasLow
namespace GlobalTheory.CovTop.MeasLow
theorem nef_share_lower_bound (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) :
    Closed FamHyp fun Fm _ => ∃ K : ℝ, 0 ≤ K ∧ EvTied Fm fun _ _ _ p => ∀ i, -(K * unitE p) ≤ Real.log (ratAt p i) := by
  obtain ⟨C, hC0, hC⟩ := _root_.MainStatements.Tam.Plug.tamagawa_pairs_product hP
  refine Closed.imp (Closed.and (Sizes.hostN 1) WtShape.wtN) ?_
  rintro eps Fm CH - ⟨⟨C1, -, hE1⟩, ⟨C2, -, hE2⟩⟩
  refine ⟨6 * C + 3, by positivity, ?_⟩
  obtain ⟨x0, hx⟩ := hE1.and hE2
  refine ⟨x0, fun x hx' hle ι p hp i => ?_⟩
  have hn := (hx x hx' hle ι p hp).1 i
  have hw := (hx x hx' hle ι p hp).2 i
  have hsz := size_le_unit p i hC0 hn hw
  have hdim := log_prod_dimAt _ i
  have hm := hC _ _ _ _ p.charW.base.lev i p.R.triv _ _ (p.charW.base.models.νW i)
  have hu0 : 0 ≤ unitE p := unit_nonneg p i hn hw
  unfold ratAt GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio
  set V := ((p.R.toRealDat.νW i) (p.R.toRealDat.fdW i)).toReal with hV
  set Q := ∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt (Fm.D x ι) i τ with hQ
  have hK0 : -((6 * C + 3) * unitE p) ≤ 0 := by nlinarith
  by_cases hV0 : V = 0
  · rw [hV0, zero_mul, Real.log_zero]; exact hK0
  by_cases hQ0 : Q = 0
  · rw [hQ0, mul_zero, Real.log_zero]; exact hK0
  have hQl : -((Fm.D x ι).R.f * (((Fm.D x ι).R.r : ℝ) ^ 2 * Real.log (((Fm.D x ι).R.r : ℝ) + 1))) ≤ Real.log Q :=
    hdim.resolve_left hQ0
  have htop : (p.R.toRealDat.νW i) (p.R.toRealDat.fdW i) ≠ ⊤ := by
    intro h; apply hV0; rw [hV, h]; rfl
  have hVe : Real.exp (-(C * (((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) ^ 2 *
      (Real.log (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r + 3) + 1) + Real.log |(discr (Fm.D x ι).host.E : ℝ)|))) ≤ V :=
    (ENNReal.ofReal_le_iff_le_toReal htop).1 hm
  have hVpos : 0 < V := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hV0)
  have hlV := Real.log_le_log (Real.exp_pos _) hVe
  rw [Real.log_exp] at hlV
  rw [Real.log_mul hV0 hQ0]
  linarith
end GlobalTheory.CovTop.MeasLow
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_lower_bound_of_cover : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Closed FamHyp fun Fm _ => ∃ K : ℝ, 0 ≤ K ∧ EvTied Fm fun _ _ _ p => ∀ i, -(K * unitE p) ≤ Real.log (ratAt p i) := by
  first | exact @_root_.GlobalTheory.CovTop.MeasLow.nef_share_lower_bound | exact _root_.GlobalTheory.CovTop.MeasLow.nef_share_lower_bound | (intros; apply _root_.GlobalTheory.CovTop.MeasLow.nef_share_lower_bound <;> assumption)
end
