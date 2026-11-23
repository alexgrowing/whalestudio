import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.E0ReadOfEigenLabelingStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemOfForall
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
noncomputable section
namespace GlobalTheory.HeightCounting.Up.IdempotentAdelicReading
theorem unramified_component_at_member_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ T w Z Wt _ t nch n c => ∀ (hC : t.r.z.R.C = TC.cf w.I w.l Z) (Xd : DivX (w.D Z)) (E : EigIdx (w.D Z) Xd) (labPi : E.Pi → (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A.fam.base.Ix) hb htup hg hf, GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector (realOfRead t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y n.tp hC Xd E labPi hb htup hg hf) := by
  intro _ hL
  exact _root_.GlobalTheory.HeightCounting.Up.CoefficientAgreement.atMem_of_forall' fun _ _ _ _ _ _ _ _ t _ _ _ _ _ _ _ _ _ _ _ =>
    goodIdempotent_eq_goodProjector_adelicReading _ _ _ _ _ _ _ _ _ _ _ _ t.r.intersectionNumber_baseChange.ok.ok2
end GlobalTheory.HeightCounting.Up.IdempotentAdelicReading
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_idempotent_reads_as_type_projector_at_member : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ T w Z Wt _ t nch n c => ∀ (hC : t.r.z.R.C = TC.cf w.I w.l Z) (Xd : DivX (w.D Z)) (E : EigIdx (w.D Z) Xd) (labPi : E.Pi → (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A.fam.base.Ix) hb htup hg hf, GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector (realOfRead t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y n.tp hC Xd E labPi hb htup hg hf) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.IdempotentAdelicReading.unramified_component_at_member_alt | exact _root_.GlobalTheory.HeightCounting.Up.IdempotentAdelicReading.unramified_component_at_member_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.IdempotentAdelicReading.unramified_component_at_member_alt <;> assumption)
end
end
