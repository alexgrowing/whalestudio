import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BcMapBcVec
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.FlatChernWeightEqOfIndependence
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.RegularFormsIsBundleProjectiveCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwistedDualRegularFormsFiniteCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CuspOnto
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.AdelicGLLastRowAndDetModuleUnderLeftMultiplicati
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.LamLevel
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.MetricStatements.SmallOnTower
import Development.AutomorphicSpectrum.Statements.MetricStatements.RankBound
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.LineDegreeClosedFormula
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.UnitarySelfGeneration

namespace YBrLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem exZ_congr {a b : WZ E} (hab : WEq Dw a b) : Rec.exZ Dw a = Rec.exZ Dw b := by
  funext i
  rcases i with _ | ⟨τ, i⟩
  · rfl
  · exact hab τ i i.2

theorem laZ_eq {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (a : WZ E) : Rec.laZ U a = GlobalTheory.AllWt.modelWt U (a, 0) := by
  funext k τ j
  simp [Rec.laZ, GlobalTheory.AllWt.modelWt]

theorem laZ_congr {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) {a b : WZ E}
    (hab : WEq Dw a b) : Rec.laZ U a = Rec.laZ U b := by
  rw [laZ_eq, laZ_eq]
  refine GlobalTheory.AllWt.modelWt_congr U hσ hU ?_
  funext i
  rcases i with _ | ⟨τ, i⟩
  · rfl
  · exact hab τ i i.2

theorem lat_secZ (a : WZ E) : Lat.secZ Xo c a 0 = Rec.secZ Xo c a := by
  have he : Lat.exZ Dw a 0 = Rec.exZ Dw a := by
    funext i
    rcases i with _ | _ <;> rfl
  ext f
  unfold Lat.secZ Rec.secZ
  rw [he]
  refine and_congr Iff.rfl (forall_congr' fun p => forall_congr' fun t => forall_congr' fun y =>
    forall_congr' fun y' => forall_congr' fun _ => ?_)
  rw [Units.coe_prod]

theorem lat_laZ {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (a : WZ E) : Lat.laZ U a 0 = Rec.laZ U a := by
  funext k τ j
  simp [Lat.laZ, Rec.laZ]

theorem lat_cuspZ (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (a : WZ E) : Lat.cuspZ U a 0 = Rec.cuspZ Xo c U a := by
  unfold Lat.cuspZ Rec.cuspZ
  simp only [lat_secZ, lat_laZ]

end YBrLat

open YBrLat in
theorem y_br_lat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (a : WZ E) (x : ℝ), (Lat.secZ Xo c a 0 = secZ Xo c a ∧ Lat.cuspZ U a 0 = cuspZ Xo c U a ∧ Lat.lieZ Dw x a = lieFacZ Dw x a ∧ ∀ f, f ∈ Lat.latZ U a 0 ↔ f ∈ cuspZ Xo c U a ∧ ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) ∧ ∀ b, WEq Dw a b → secZ Xo c a = secZ Xo c b ∧ cuspZ Xo c U a = cuspZ Xo c U b ∧ lieFacZ Dw x a = lieFacZ Dw x b ∧ towerWt Dw a = towerWt Dw b ∧ (∀ σ, GoodEmb c σ → laZ (U σ) a = laZ (U σ) b) ∧ ∀ Z, cuspOn U h a Z = cuspOn U h b Z ∧ latOn U h a Z = latOn U h b Z := by
  intro E _ _ _ H Dw l Xo c r U h e L a x
  refine ⟨⟨lat_secZ a, lat_cuspZ U a, rfl, fun f => ?_⟩, fun b hab => ?_⟩
  · rw [Lat.mem_latZ, lat_cuspZ]
  have h1 : Rec.secZ Xo c a = Rec.secZ Xo c b := by
    unfold Rec.secZ; rw [exZ_congr hab]
  have h2 : ∀ σ, GoodEmb c σ → Rec.laZ (U σ) a = Rec.laZ (U σ) b := fun σ hσ =>
    laZ_congr (U σ) hσ (L.unf σ hσ) hab
  have h3 : Rec.cuspZ Xo c U a = Rec.cuspZ Xo c U b := by
    unfold Rec.cuspZ
    rw [h1]
    exact congrArg (Rec.secZ Xo c b ⊓ ·) (iInf_congr fun σ => iInf_congr fun hσ => by rw [h2 σ hσ])
  have h4 : ∀ Z, Rec.cuspOn U h a Z = Rec.cuspOn U h b Z := fun Z => by
    unfold Rec.cuspOn; rw [h3]
  refine ⟨h1, h3, ?_, ?_, h2, fun Z => ⟨h4 Z, ?_⟩⟩
  · have : (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) =
        ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (b (τ, i) : ℝ) :=
      Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => by rw [hab τ i i.2]
    unfold Rec.lieFacZ
    rw [this]
  · funext τ n
    have hn := n.2
    unfold towerWt
    split_ifs with hp
    · rw [hab τ.1 n (by rw [Datum.mult, if_pos τ.2]; exact hp)]
    · rw [hab (conjEmb τ.1) _ (by rw [Datum.mult, if_neg (GlobalTheory.AllWt.conj_not_mem τ)]; omega)]
  · unfold Rec.latOn; rw [h4 Z]

end PositivityTheory.UnitarySelfGeneration
