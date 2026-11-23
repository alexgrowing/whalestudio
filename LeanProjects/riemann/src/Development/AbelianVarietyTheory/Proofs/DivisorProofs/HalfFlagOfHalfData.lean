import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorAtZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorAtMulTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartMinorValuationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartHeightBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartNormComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartSectionDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartDegreeFormulaStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MvPolynomial Formalism.BasicNotions.DV
open GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag
open GlobalTheory.Cartier GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.WholeFlag
open IsDedekindDomain GlobalTheory.WholeFlag.Glue
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WholeFlag.GlueProof

theorem halfFlag_of_halfDataC {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ}
    (A : Fin g → Adl C Y) (p : ℕ) (hp : p.Prime) (hD : HalfDataC A p) : HalfFlag A p := by
  obtain ⟨V, W, ι, U, H, J, d, T, L, m, hJ, hW, hm, hcov, hLcov, hT, hgd, hN, hreg, htest⟩ := hD
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · refine ⟨V, W, ι, U, fun _ => 0, J, fun _ i => i.elim0, hJ, hW, hcov, fun a x _ _ => ⟨fun i => i.elim0, ?_⟩,
      fun a i => i.elim0, fun v _ e y _ z yt _ _ a _ => ⟨fun i => i.elim0, fun i => i.elim0, fun b _ k => k.elim0⟩⟩
    haveI : IsEmpty (Fin (0 + 0)) := ⟨fun i => i.elim0⟩
    rw [Matrix.det_isEmpty]
    exact unitAt_one x
  choose r hr1 hr2 hr3 using hN
  have hyp : Hyp A p V W U H J d T L m r :=
    ⟨hp, hg, hJ, hW, hm, hcov, hLcov, hT, hgd, hr2, fun i v hv e y z yt c h1 h2 h3 => hr3 i v hv e y trivial z yt c h1 h2 h3,
      hreg, htest⟩
  refine ⟨V, W, Idx ι L, chartOpen V U H L m r, chartM V H J, J, chartC V H, hJ, hW,
    GlobalTheory.T.hodge_chart_minor_valuation A p V W U H J d T L m r hyp, GlobalTheory.T.hodge_chart_height_bound A p V W U H J d T L m r hyp, GlobalTheory.T.hodge_chart_norm_comparison A p V W U H J d T L m r hyp, ?_⟩
  intro v hv e y hy z yt hz hyt q hq
  exact ⟨(GlobalTheory.T.hodge_chart_section_divisor A p V W U H J d T L m r hyp v hv e y hy z yt hz hyt q hq).1,
    (GlobalTheory.T.hodge_chart_section_divisor A p V W U H J d T L m r hyp v hv e y hy z yt hz hyt q hq).2,
    fun b hb k i => GlobalTheory.T.hodge_chart_degree_formula A p V W U H J d T L m r hyp v hv e y hy z yt hz hyt q b hq hb k i⟩

end GlobalTheory.WholeFlag.GlueProof
