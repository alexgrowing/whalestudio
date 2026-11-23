import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBigCellCoordinateJacobianVerticalChangesEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_bigCellCoordinateJacobian_verticalChanges_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (K : Type) [Field K] (M : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K), (∀ σ i j, j < i → M σ i j = 0) → (∀ σ i, M σ i i = 1) → (Matrix.of fun a b : VIx Dw => ((GlobalTheory.FlagTan.unip K (Pi.single b.toF (1 : K)) a.1 * (M a.1).map (fun r => (TrivSqZeroExt.inl r : DualNumber K))) a.2.1.1 a.2.1.2).snd).det = 1 := by
  first | exact @GlobalTheory.LogPole.VertDet.det_vert | exact GlobalTheory.LogPole.VertDet.det_vert | (intros; apply GlobalTheory.LogPole.VertDet.det_vert <;> assumption)
