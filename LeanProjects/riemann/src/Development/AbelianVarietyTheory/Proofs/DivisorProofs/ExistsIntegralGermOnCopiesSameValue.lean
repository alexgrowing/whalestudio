import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthNonnegIntegralOperatorIntegralVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmSumIntegralAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActionLinearLogCoordinatesIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogIntegralUnitsSubgroupExpHomProofStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonGaugeBiadditiveOfLogSumActionLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameSeriesExpSumOfActionLinearLogUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugeHermitianCombinationOfStepsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesCoeffUniformlyContinuousInCoeffsProofStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitActionIntegralPointOfStepsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitIsotropicFrameIntegralOfStepsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeIdempotentApproximationsDVRProofStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitEntriesMatrixInverseClosedProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationEqPartialLogCoordsProofStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstCoeffOperatorLinearSubstitutionProofStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitActionLieAlgebraOfPrimeIdempotentApproxStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaOperatorFrameSeriesOfStepsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionIntegralOfLimitStepsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionRetractionOfLimitStepsStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ColumnGerm

open NumberField MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns GlobalTheory.IsoTriv

theorem mvIsInt_pow {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {σ : Type} {g : MvPowerSeries σ C}
    (hg : MvIsInt v g) (k : ℕ) : MvIsInt v (g ^ k) := by
  classical
  induction k with
  | zero =>
    intro α
    unfold IsIntV
    rw [pow_zero, coeff_one]
    split_ifs <;> simp
  | succ k ih => rw [pow_succ]; exact GlobalTheory.DepthNonneg.mvIsInt_mul ih hg

theorem exists_nabX_eq (hN : NabSt) (hI : InclSt) (hR : RetrSt) (hU : UnitSt) (hF : FrameSt)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} [StarRing (𝓞 E)] (hs : ∀ a : 𝓞 E, star a = H.bar a)
    {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (Ch : IntegralChartA3 Xo c T io y)
    {p : ℕ} [Fact p.Prime] (X : ValExt T p) (cx : Lt1 Dw → ℕ) {n : ℕ} (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V)
    (hB : IsCols c T io p cx B) (k : ℕ) (f : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C)
    (hf : MvIsInt (vX_vp X) f) :
    ∃ g : PS X.C n (chD Ch.ch), MvIsInt (vX_vp X) g ∧
      nabX Ch X cx B k g = derivAt0 (polyH X.C cx) (subst (expH Ch X cx) f) := by
  obtain ⟨ψ, ψ0, -, ψe, ψU⟩ := hI E H Dw l Xo c hs T io y Ch p X cx n B hB
  obtain ⟨ρ, ρ0, ρi, ρe⟩ := hR E H Dw l Xo c hs T io y Ch p X cx n B hB
  have hψ : HasSubst ψ := hasSubst_of_constantCoeff_zero ψ0
  have hρ : HasSubst ρ := hasSubst_of_constantCoeff_zero ρ0
  have e0 : ∀ q, constantCoeff (expH Ch X cx q) = 0 := fun q =>
    cc_expPt (fgl Ch X) (fun e => by simp) q.2
  have c0 : ∀ q, constantCoeff (colPt Ch X cx B q) = 0 := fun q =>
    cc_expPt (fgl Ch X) (fun e => by simp) q.2
  have he : HasSubst (expH Ch X cx) := hasSubst_of_constantCoeff_zero e0
  have hc : HasSubst (colPt Ch X cx B) := hasSubst_of_constantCoeff_zero c0
  have fr1 : constantCoeff (frameX Ch X n) = 1 := by
    letI := io.toAlgebra
    letI : Algebra T.Fr X.C := X.ιF.toAlgebra
    exact (hF X.C (vX_vp X) _ T.Fr (𝓞 E) Ch.ch.B (isIntFB_chart Ch X) _ (gauge_chart Ch X) H.w0 n).1
  have U1 : constantCoeff (subst ψ (frameX Ch X n) : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C) = 1 := by
    have h := constantCoeff_subst_eq_zero hψ ψ0 (f := frameX Ch X n - 1) (by rw [map_sub, fr1, map_one, sub_self])
    rw [← coe_substAlgHom hψ, map_sub, map_one, map_sub, map_one, sub_eq_zero, coe_substAlgHom] at h
    exact h
  obtain ⟨U', U'i, hU'⟩ := (hU X.C (vX_vp X) _).2.2.2.2.2 _ ψU U1
  refine ⟨subst ρ (f * U' ^ k), ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst _
    (GlobalTheory.DepthNonneg.mvIsInt_mul hf (mvIsInt_pow U'i k)) ρi ρ0, ?_⟩
  rw [hN E H Dw l Xo c T io y Ch p X cx n B k]
  congr 1
  have h1 : subst (colPt Ch X cx B) (subst ρ (f * U' ^ k) : PS X.C n (chD Ch.ch)) =
      subst (expH Ch X cx) (f * U' ^ k) := by
    rw [subst_comp_subst_apply hρ hc, funext ρe]
  have h2 : subst (colPt Ch X cx B) (frameX Ch X n) = subst (expH Ch X cx)
      (subst ψ (frameX Ch X n) : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C) := by
    rw [subst_comp_subst_apply hψ he, funext ψe]
  rw [subst_mul hc, subst_pow hc, h1, h2, ← subst_pow he, ← subst_mul he, mul_assoc, ← mul_pow, mul_comm U', hU',
    one_pow, mul_one]

end GlobalTheory.ColumnGerm

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ColumnGerm

theorem exists_germ_on_copies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p cx B → ∀ (N k : ℕ) (f : MvPowerSeries (Σ _ : GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.Col cx, Fin (chD Ch.ch)) X.C), MvIsInt (vX_vp X) f → ∃ g : PS X.C n (chD Ch.ch), MvIsInt (vX_vp X) g ∧ (((N : ℝ) : ℝ) : WithTop ℝ) ≤ vX_vp X (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nabX Ch X cx B k g - derivAt0 (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.polyH X.C cx) (MvPowerSeries.subst (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.expH Ch X cx) f)) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ la T io e _ y Ch X cx n B hB N k f hf
  have hadd := GlobalTheory.T.logarithm_sum_integral_additive
  have hact := GlobalTheory.T.action_linear_logCoordinates_integral
  have hunit := GlobalTheory.T.logIntegralUnitsSubgroupExpHom_proof
  have hcont := GlobalTheory.T.seriesCoeffUniformlyContinuousInCoeffs_proof
  have hbi := GlobalTheory.T.canonGaugeBiadditive_of_logSum_actionLinear hadd hact
  have hfr := GlobalTheory.T.frameSeriesExpSum_of_actionLinear_logUnit hact hunit
  have hfin := GlobalTheory.T.gaugeHermitianCombination_of_steps hadd hact hunit hbi
  have hla := GlobalTheory.T.limitActionLieAlgebra_of_primeIdempotentApprox GlobalTheory.T.primeIdempotentApproximationsDVR_proof
  have hlp := GlobalTheory.T.limitActionIntegralPoint_of_steps hadd hact hcont
  have hlf := GlobalTheory.T.limitIsotropicFrameIntegral_of_steps hadd hact hunit hbi hfr hfin hcont
  obtain ⟨g, hg, h⟩ := exists_nabX_eq (GlobalTheory.T.nablaOperatorFrameSeries_of_steps GlobalTheory.T.invariantDerivationEqPartialLogCoords_proof GlobalTheory.T.constCoeffOperatorLinearSubstitution_proof hfr) (GlobalTheory.T.columnInclusionIntegral_of_limitSteps hla hlp hlf)
    (GlobalTheory.T.columnInclusionRetraction_of_limitSteps hla hlp GlobalTheory.IsoTriv.limitEntriesMatrixInverseClosed_proof) hunit hfr (fun _ => rfl) Ch X cx B hB k f hf
  refine ⟨g, hg, ?_⟩
  rw [h, sub_self, AddValuation.map_zero]
  exact le_top

end GlobalTheory.ColumnGerm
