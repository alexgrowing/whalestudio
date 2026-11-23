import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AtMemAnd
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc
theorem atMem_and' {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (hp : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p) (hq : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun K B f T w Z Wt p0 t nch n c => p K B f T w Z Wt p0 t nch n c ∧ q K B f T w Z Wt p0 t nch n c := by
  refine (hp.inter hq).imp fun K _ _ _ _ H => ?_
  refine (H.1.inter H.2).imp fun B f T _ H => ?_
  intro hK w Z Wt p0 t nch n xd c hE hX hC
  exact ⟨H.1 hK w Z Wt p0 t nch n xd c hE hX hC, H.2 hK w Z Wt p0 t nch n xd c hE hX hC⟩
theorem atMem_mono {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (hp : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p)
    (h : ∀ K B f T w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c) →
      p K B f T w Z Wt p0 t nch n c → q K B f T w Z Wt p0 t nch n c) : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q := by
  refine hp.imp fun K _ _ _ _ H => ?_
  refine H.imp fun B f T _ H => ?_
  intro hK w Z Wt p0 t nch n xd c hE hX hC
  exact h K B f T w Z Wt p0 t nch n xd c hE (H hK w Z Wt p0 t nch n xd c hE hX hC)
end GlobalTheory.GalLoc
end
