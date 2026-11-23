import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CPAsIdeal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChiSRfl
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTIota
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjChar

open Formalism.L2.SG.HidaSetting in

theorem argT_finE_eq {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (κ : GA D (Yc D 0)) :
    argT X h (finE (Yc D 0) κ) = cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) h)
      (GlobalTheory.FlagBasis.chiArg X.B.I X.e0 X.f0 X.z0 X.bw X.bwd ((iotaX X h).toMulEquiv κ).2) := by
  obtain ⟨⟨I⟩⟩ := X
  dsimp only at h
  subst h
  have e := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
  have e2 : finE (Yc D 0) κ = ((Formalism.IndefR.RationalEmbedding.iota D κ).2.1 : GL (Fin (D.sp.Y 0).rank) (EAf D)) :=
    (congrArg (finE (D.sp.Y 0)) ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ)).symm.trans e
  rw [e2]
  rfl

theorem intAf_cast {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (c : TensorProduct X.B.I.F X.B.I.E (Formalism.MainNotions.S.Af X.B.I.F)) (hc : c ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) :
    cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) h) c ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨⟨I⟩⟩ := X
  dsimp only at h
  subst h
  exact hc

theorem chiS_cast {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (c : TensorProduct X.B.I.F X.B.I.E (Formalism.MainNotions.S.Af X.B.I.F)) :
    chiS X h (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) h) c) =
      X.psiEf (Formalism.L2.SG.HidaSetting.divN X.B.I X.B.g c) := by
  rw [chiS_rfl]
  congr 2
  exact cast_cast _ _ c |>.trans (cast_eq _ c)

end GlobalTheory.SeeConjChar

namespace GlobalTheory.SeeConjChar

theorem argT_mem_intAf_and_chi2_eq_chiS_of_mem_Kset : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (κ : GA D (Yc D 0)), ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset → GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ X.chi2 ((iotaX X h).toMulEquiv κ).2 = GlobalTheory.SeeConjChar.chiS X h (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ)) := by
  intro D X h κ hK
  rw [argT_finE_eq X h κ]
  refine ⟨intAf_cast X h _ ?_, ?_⟩
  · obtain ⟨hef, hz0, hb⟩ := X.vectorsInLattice
    have hnxt : ∀ a, Formalism.L2.SG.HidaSetting.nxt X.e0 X.z0 a ∈ X.B.I.Lf := fun a => by
      unfold Formalism.L2.SG.HidaSetting.nxt
      split_ifs
      exacts [(hef _).1, hz0]
    unfold GlobalTheory.FlagBasis.chiArg
    refine Subring.add_mem _ (Subring.sum_mem _ fun a _ => ?_) (Subring.sum_mem _ fun i _ => ?_)
    · exact Formalism.L2.SG.Pf.unitaryCongruence.hA_int _ (hef a).2 (Formalism.L2.SG.Pf.unitaryCongruence.K_mv _ hK (hnxt a))
    · split_ifs with hi
      · exact Formalism.L2.SG.Pf.unitaryCongruence.hA_int _ (hb i).2 (Formalism.L2.SG.Pf.unitaryCongruence.K_mv _ hK (hb _).1)
      · exact Subring.zero_mem _
  · exact (chiS_cast X h _).symm

end GlobalTheory.SeeConjChar
