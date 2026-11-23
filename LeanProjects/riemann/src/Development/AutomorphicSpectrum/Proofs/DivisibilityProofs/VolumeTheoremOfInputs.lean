import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBounds
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LinkedTowerPowerSumStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropFTopHoldsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AgreementPositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AntisymmetryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CoefficientsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagHeightStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NefPolarizationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProportionalStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerRealConditionsStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerI5Statement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerGlobalConditionsStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerM1NefStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerM2Statement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerGlobalExtraStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerRealI6Statement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerRealExtraStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerRealAgreementStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerIntersectionExtraStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerA1Statement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerConvI2Statement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerI1Statement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FullIntersectionTowerI8IdentityStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerNefGeneralStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerProportionalStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelNefFibresStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SlopeLowerBaseSettingsStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerWeilInputsCombinedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BaseSettingOfGoodTowerStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TestPolynomialShiftTotalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem slopeLower_mono_top {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (T : Top.RootTower Ψ N)
    (II : IntersectionSystem) {C C' rd Lval : ℝ} (hCC : C ≤ C') (hrd : 1 ≤ rd) (hP : T.Proportional)
    (h : T.SlopeLower II C rd Lval) : T.SlopeLower II C' rd Lval := by
  intro B hB hB' hbad
  have h1 := h B hB hB' hbad
  have hJ : 0 < Top.testDeg Ψ N T.j := (GlobalTheory.T.test_polynomial_shift_total Ψ N T.j T.j_pos T.j_lt).2.1
  have hvol : 0 ≤ T.volT := Finset.sum_nonneg fun c _ => (hP.1 c).le
  have hB1 : (128 : ℝ) ≤ B := by exact_mod_cast hB
  have hL : 0 ≤ Top.bigLam B rd Lval := by
    unfold Top.bigLam
    have h2 : (1 : ℝ) ≤ B * rd := by nlinarith
    have := Real.log_nonneg h2
    positivity
  have hK : 0 ≤ (Fintype.card Ψ : ℝ) * ((min T.j (N - T.j) : ℕ) : ℝ) * Top.bigLam B rd Lval *
      (((Top.dimX Ψ N T.j : ℝ) + 1) * (T.volT * Top.testDeg Ψ N T.j)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hCC hK]

theorem volumeTheoremX_of_inputs : Top.Given → PtsIntegrableStatement → Out.WeilSt → (∃ Ch Cu : ℝ, NineGeoU Ch Cu) →
    HodgeLatticeFlagBound → TrivFlagOnHodge → Fl.FlatDegree → TwistAut → Cmp.CmpPair → Cmp.CmpSt → Top.VolumeTheoremX := by
  intro hG hPts hW hNineE hM3 hTF hFD hTw hCP hCS
  obtain ⟨Ch, Cu, hNine⟩ := hNineE
  obtain ⟨-, -, -, -, -, -, -, -, -, hIn, hHS, -, hNF, hAP⟩ := id hG
  obtain ⟨hZ1, hZ2, -⟩ := hHS
  obtain ⟨hZh, -, -, -, hGr⟩ := hNF
  have hAg := GlobalTheory.T.agreement_positive
  refine ⟨2 * max (Ch + Cu / 2) 0 + 3 * 4 + 5, by positivity, ?_⟩
  intro E _ _ _ _ H D Xo l c Y _ T o II hGl hX hII hq hpq hbad
  obtain ⟨hrd, hne, -⟩ := GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H
  haveI := hne
  have hp : 1 ≤ D.p := by omega
  have hqp : D.q ≤ D.p := by omega
  have hUnif := GlobalTheory.T.good_tower_real_agreement hG E H D Xo l c Y T o II hGl hX hII hp hq
  have hProp : T.Proportional := GlobalTheory.T.real_tower_proportional GlobalTheory.T.proportional' hIn II hII _ _ T _ hUnif
  have hCI := GlobalTheory.T.real_tower_conv_I2 hAg hIn II hII _ _ T (Top.realOf o.toTowerOrigin)
  have hI1 := GlobalTheory.T.real_tower_I1 GlobalTheory.T.coefficients' hAg hIn II hII _ _ T _
    (GlobalTheory.T.good_tower_real_I6 hG E H D Xo l c Y T o II hGl hX hII hp hq)
  have hPos : (Top.realOf o.toTowerOrigin).Pos := fun a => (o.Fx a).pos
  have hA1 := GlobalTheory.T.real_tower_A1 hIn II hII _ _ T _ o.smooth o.flat hPos
  have hM1 := GlobalTheory.T.good_tower_M1_nef hG E H D Xo l c Y T o II hGl hII hp hq
  have hM2 := GlobalTheory.T.good_tower_M2 hG E H D Xo l c Y T o II hGl hII hp hq
  have hAN : T.ANef := fun B a => GlobalTheory.T.root_model_nef_fibres _ _ (T.M B a) fun k => by
    obtain ⟨h1, h0⟩ := (o.Or B a).A_deg
    by_cases hk : k = (o.Or B a).k₀
    · rw [hk, h1]; norm_num
    · rw [h0 k hk]
  have hI56 := GlobalTheory.T.good_tower_I5 hG E H D Xo l c Y T o II hGl hX hII hp hq
  have hI7 : T.I7 := fun B a =>
    ⟨(GlobalTheory.T.real_tower_nef_general GlobalTheory.T.nef_polarization hIn II hII _ _ T _ o.smooth o.flat B a).1,
      (GlobalTheory.T.real_tower_nef_general GlobalTheory.T.nef_polarization hIn II hII _ _ T _ o.smooth o.flat B a).2,
      GlobalTheory.T.good_tower_real_conditions hG E H D Xo l c Y T o II hGl hX hII hp hq B a⟩
  have hI8 := GlobalTheory.T.full_intersection_tower_I8_identity hCS hG hW E H D Xo l c Y T o II hX hII hp hq
  obtain ⟨φ, hfs, hLk⟩ := GlobalTheory.T.good_tower_global_conditions hCS hAg hM3 hTF hG E H D Xo l c Y T o II hGl hX hII hp hq
  have hP6 := GlobalTheory.T.linked_tower_power_sum _ _ T II hII.1 hProp φ hLk
  have hPA := GlobalTheory.T.good_tower_propA_of_global_extra hAg hTw hCP hG E H D Xo l c Y T o II hGl hX hII hp hq
  have hbadP : ∀ p ∈ T.bad, p.Prime := fun p hp' => ((o.bad_iff p).1 hp').1
  have hPF := GlobalTheory.T.PropFTop_holds hPts hIn.2.2.1.2 hIn.2.1.2.1 _ _ T II _ (hostRd E) (hostLval H) hII.1 hCI.1 hProp hP6
    (by linarith) hbadP (GlobalTheory.T.good_tower_real_extra hFD hG E H D Xo l c Y T o II hGl hX hII hp hq)
  have hVol := GlobalTheory.T.good_tower_intersection_extra hCS hG E H D Xo l c Y T o II hGl hX hII hq hpq
  have hj3 : 3 * (D.p + D.q - T.j) + 1 ≤ D.p + D.q := by rw [o.j_eq]; omega
  have hSL0 := GlobalTheory.T.slope_lower_base_settings hZh II hII.1 _ _ T Ch Cu (hostRd E) (hostLval H) hProp hj3
    fun B _ hB _ a => GlobalTheory.T.base_setting_of_good_tower Ch Cu hNine hW hAg GlobalTheory.T.proportional' hCS hG hPts E H D Xo l c Y T o II hGl hX hII
      hp hq hqp hbad B hB a
  have hSL := slopeLower_mono_top T II (le_max_left (Ch + Cu / 2) 0) (by linarith) hProp hSL0
  have hch := GlobalTheory.T.tower_weil_inputs_combined GlobalTheory.T.flag_height hIn hZ1 hZ2 hAP hGr II hII _ _ T _ (max (Ch + Cu / 2) 0) 4 (hostRd E)
    (hostLval H) (le_max_right _ _) (by norm_num) (by linarith) hfs hProp hI1 hCI.2 hA1 hM1 hM2 hAN hI56.1 hI56.2
    hI7 hI8 hP6 hPA hPF hVol hSL
  exact ⟨hProp, hVol, hch.1, hch.2.1, hch.2.2.1, hch.2.2.2⟩

end GlobalTheory.CompanionTheory.Ar.Cusp
