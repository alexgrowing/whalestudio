import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ)
def extensionWithList : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL := fun K B f T w Z Wt p0 t nch n xd c => _root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c ×
  PLift (ListPin (w.st Z).toD7 t.r.z.R.toRealDat.toLevCh cDep K.s.b)
def SettingsFormsExistList' : Prop := AllSt fun _ _ _ _ _ P x => _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevel hL x') ∧ ListSt cDep x'
def SeriesExistList' : Prop := AllSt fun _ _ _ _ _ P x => _root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevel hL x → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x') ∧ (ListSt cDep x → ListSt cDep x')
def ModuliPointsExistList' : Prop := AllSt fun _ _ _ _ _ P x => _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x') ∧ (ListSt cDep x → ListSt cDep x')
def FinitenessListStatement : Prop := AllSt fun K _ _ _ w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (S : SExt) (Γ : GeoP), ListSt cDep x →
  ∃ (Z : w.Lt) (v : Lv3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) S Γ).s K w Z), v.Wt = P.Wt ∧ Kept l.c.ch v.nch
end GlobalTheory.HeightCounting.Up
end
end
