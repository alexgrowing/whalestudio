import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 2000000
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
structure SameGaloisLevel (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (x : St P) : Type 1 where
  a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL (Dof x) (cfOf x) (repOf x.r.Y)
  Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (Dof x).host.E)) → PlE (Dof x).host
  Pq_over : ∀ v, NG.OverPl (Pq v) v
  sel : Set.range Pq = Set.range w.I.sel
structure IntermediateLevel (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (x : St P) : Type 1 extends toLA : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x where
  mt : InMt x.r.Y (cfOf x) w.I.xi (QOf P)
  rat : InRat x.r.Y x.m.z.cG
  cusp : RowCusp (Dof x) a.A.row
structure FirstIntermediateLevel (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (x : St P) : Type 1 extends toLI : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x where
  b : _root_.GlobalTheory.HeightCounting.SettingsFormsData a rat Pq
structure SecondIntermediateLevel (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (x : St P) : Type 1 extends toLI : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x where
  b : _root_.GlobalTheory.HeightCounting.SeriesData x.m.z.geo a rat mt.ad.PV Pq
structure ThirdIntermediateLevel (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (x : St P) : Type 1 extends toLI : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x where
  b : _root_.GlobalTheory.HeightCounting.ModuliPointsData x.m.z.geo a rat mt.ad.PV Pq
structure StrictHenselianAcyclicLevel (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (x : St P) : Type 1 extends toStrictHenselianAcyclic : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x where
  c : _root_.GlobalTheory.HeightCounting.HeightCountingCharacterData mt b T.k T.psi
variable (hL)
def extensionWithLaw : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL := fun K B f T w Z Wt p0 t nch n xd c => _root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c × PLift (BkLaw (w.D Z))
def SameGaloisLevelExists : Prop := AllSt fun _ _ _ _ _ P x => IsEmpty x.o.N.nd.Loc →
  ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x') ∧ GlobalTheory.TwistChoice.SameGalois (Dof x).nd (Dof x').nd
def RationalityStatementThirdPlaceSeries : Prop := AllSt fun _ _ _ _ _ _ x => _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → Nonempty (InRat x.r.Y x.m.z.cG)
def CuspStatement' : Prop := AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x, RowCusp (Dof x) l.a.A.row
def FirstIntermediateLevelExists : Prop := AllSt fun _ _ _ _ _ P x => _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevel hL x')
def SecondIntermediateLevelExists : Prop := AllSt fun _ _ _ _ _ P x => _root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevel hL x → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x')
def ThirdIntermediateLevelExists : Prop := AllSt fun _ _ _ _ _ P x => _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x')
def StrictHenselianAcyclicLevelNonempty : Prop := AllSt fun _ _ _ T _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x, Nonempty (_root_.GlobalTheory.HeightCounting.HeightCountingCharacterData l.mt l.b T.k T.psi)
def EtaStatement' : Prop := AllSt fun _ _ _ _ _ P x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x,
  _root_.GlobalTheory.CoefDuty.AutomorphicSideExists l.a.A l.mt.M l.c.ch l.c.tp.tup → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' =>
    GlobalTheory.CoefDuty.Large D' ∧ ∀ j v, 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : D'.what₂.places.Pl, HEq v' v → D'.what₂.etaJ j v' = P.q.eta j v
def FinitenessStatement : Prop := AllSt fun K _ _ _ w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (S : SExt) (Γ : GeoP),
  ∃ (Z : w.Lt) (v : Lv3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL) S Γ).s K w Z), v.Wt = P.Wt ∧ Kept l.c.ch v.nch
end GlobalTheory.HeightCounting.Up
end
end
