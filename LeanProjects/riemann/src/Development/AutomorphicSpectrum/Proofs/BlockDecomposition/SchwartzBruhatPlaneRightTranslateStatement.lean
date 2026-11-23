import Mathlib
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetInd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatPlaneRightTranslate
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

theorem _root_.GlobalTheory.T.schwartz_bruhat_plane_right_translate : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (Ψ : F × F → ℂ), GlobalTheory.CompanionTheory.WS.IsSB Ψ → ∀ g : GL (Fin 2) F, GlobalTheory.CompanionTheory.WS.IsSB (Ψ ∘ GlobalTheory.CompanionTheory.WS.rowAct g) := by
  first | exact @GlobalTheory.CompanionTheory.WS.Comp.isSB_comp_rowAct | exact GlobalTheory.CompanionTheory.WS.Comp.isSB_comp_rowAct | (intros; apply GlobalTheory.CompanionTheory.WS.Comp.isSB_comp_rowAct <;> assumption) | exact @GlobalTheory.CompanionTheory.WS.Comp.isSB_comp_rowAct | exact GlobalTheory.CompanionTheory.WS.Comp.isSB_comp_rowAct | (intros; apply GlobalTheory.CompanionTheory.WS.Comp.isSB_comp_rowAct <;> assumption) | exact @GlobalTheory.CompanionTheory.WS.Comp.continuous_rowAct | exact GlobalTheory.CompanionTheory.WS.Comp.continuous_rowAct | (intros; apply GlobalTheory.CompanionTheory.WS.Comp.continuous_rowAct <;> assumption) | exact @GlobalTheory.CompanionTheory.WS.Comp.rowAct_one | exact GlobalTheory.CompanionTheory.WS.Comp.rowAct_one | (intros; apply GlobalTheory.CompanionTheory.WS.Comp.rowAct_one <;> assumption) | exact @GlobalTheory.CompanionTheory.WS.Comp.rowAct_rowAct | exact GlobalTheory.CompanionTheory.WS.Comp.rowAct_rowAct | (intros; apply GlobalTheory.CompanionTheory.WS.Comp.rowAct_rowAct <;> assumption)
