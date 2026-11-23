import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEigenIndexLabelingAtMemberStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
noncomputable section
namespace GlobalTheory.HeightCounting.Up.IdxAt
theorem exists_divisor_eigenvalueIndex_labeling_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ T w Z Wt _ t _ _ _ => ∃ (Xd : DivX (w.D Z)) (E : EigIdx (w.D Z) Xd), Nonempty (E.Pi → (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A.fam.base.Ix) := by
  intro _ hL
  have e0 : EvLgG fun _ _ _ _ => True :=
    evG_good.imp fun _ _ _ _ _ _ => ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp,
      fun _ _ _ _ _ _ _ => trivial⟩
  unfold _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint
  refine e0.imp fun K _ _ _ _ hK => ?_
  refine hK.imp fun B f T _ _ _ w Z Wt p0 t nch n xd c _ _ _ => ?_
  letI : Algebra (↥t.r.z.core.Q.c.F) (w.D Z).what₂.LL := t.r.z.alg
  refine ⟨GlobalTheory.Mem.Top.DivRec.x0 t.r.Z t.r.z.pins t.r.intersectionNumber_baseChange, GlobalTheory.eigIdxFiniteTypes _ _, ⟨fun σ => ?_⟩⟩
  have hc := (t.r.intersectionNumber_baseChange.ok.ok2.what₂ (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A.μ0).comm
  let p := GlobalTheory.Mem.Top.DivRec.labOf t.r.Z t.r.intersectionNumber_baseChange σ
  exact ⟨p.1.1, Formalism.L2.DIV.InertDat3.mem_ixFin_fst _ hc p.2⟩
end GlobalTheory.HeightCounting.Up.IdxAt
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigIdx_labeling_at_member : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ T w Z Wt _ t _ _ _ => ∃ (Xd : DivX (w.D Z)) (E : EigIdx (w.D Z) Xd), Nonempty (E.Pi → (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A.fam.base.Ix) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.IdxAt.exists_divisor_eigenvalueIndex_labeling_alt | exact _root_.GlobalTheory.HeightCounting.Up.IdxAt.exists_divisor_eigenvalueIndex_labeling_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.IdxAt.exists_divisor_eigenvalueIndex_labeling_alt <;> assumption)
end
end
