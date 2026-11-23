import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetNumberUpperWeight
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsAtPointStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumbersAtPoint

set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RefSum.JetsUb
open GlobalTheory.AllWt GlobalTheory.CompHS
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end GlobalTheory.RefSum.JetsUb
theorem GlobalTheory.RefSum.JetsUb.jetNum_ub_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP _ => (i : ℕ) + 1 < (Fm.D x ι).R.m → GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub (GlobalTheory.RefSum.nCol (dat p i)))) (1 / 2500) := by
  intro hS
  refine Formalism.MainNotions.Closed.imp (Formalism.MainNotions.Closed.and (Formalism.MainNotions.Closed.and hS (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hS)) (_root_.GlobalTheory.RefSum.NumPtAlt.numbers_at_point hS)) ?_
  rintro eps Fm CH - ⟨⟨⟨_, _, hA⟩, ⟨_, _, hB⟩⟩, ⟨_, _, hC⟩⟩
  obtain ⟨x0, h⟩ := _root_.GlobalTheory.CovTop.EventuallyAtAllPoints.and (_root_.GlobalTheory.CovTop.EventuallyAtAllPoints.and hA hB) hC
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi => ?_⟩
  obtain ⟨⟨hA, hB⟩, hC⟩ := h x hx hle ι p hp
  obtain ⟨⟨u1, hu⟩, -⟩ := (hA i).2.2.2.2.2.2 hi
  obtain ⟨hp1, -, -, hq, hanti, -⟩ := hB i hi
  have j := (hC i hi u1 hu).1
  rw [hq u1 hu] at j
  exact j.of_le (GlobalTheory.RefSum.JetsUb.DF_ub_le _ _ hp1 fun τ => (hanti τ).1.antitone)
end
end
