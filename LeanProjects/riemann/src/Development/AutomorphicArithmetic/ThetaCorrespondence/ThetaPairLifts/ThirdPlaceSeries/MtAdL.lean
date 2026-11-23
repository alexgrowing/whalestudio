import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMotiveAdjointWithLevels
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalMultiplicityFamily
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Fin3
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
theorem exists_mtAd_psi_vector_of_yRel {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
    {x : St P} (L : LocAll (lay0 (Dof x))) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0) (hY : YRel L Y) :
    ∃ ad : MtAd Y (_root_.GlobalTheory.HeightCounting.Fin3.localMultiplicityFamily L l), ad.PV = _root_.GlobalTheory.HeightCounting.Fin3.psiVectorLocal L l := by
  refine ⟨{ PV := _root_.GlobalTheory.HeightCounting.Fin3.psiVectorLocal L l
            std := (by with_unfolding_all exact (l.mt.ad.std :))
            eW := (by with_unfolding_all exact (l.mt.ad.eW :))
            read := fun μ h i y g => ?_
            rat := (by with_unfolding_all exact (l.mt.ad.rat :))
            wt := (by with_unfolding_all exact (l.mt.ad.wt :))
            id := (by with_unfolding_all exact (l.mt.ad.id :)) }, rfl⟩
  have h1 := l.mt.ad.read ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (y :))) ((by with_unfolding_all exact (g :)))
  have h2 := hY.jMt μ h i y
  kexactB h1.trans (congrFun (eq_of_heq h2) _).symm
end GlobalTheory.HeightCounting.Fin3
end
end
