import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CPAsIdeal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemDeeperLevelIffReductionsSymmetricUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairTable
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingVectorsIntegralInFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OtherInstanceCharacterEqConjInstancePsiValueInte
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubOneIffEntries
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SeeConjRead

noncomputable section
namespace GlobalTheory.SeeConjChar
open Classical

theorem hT_pairAt_int : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ (PP : Pl D.host.E) (a : Fin (Yc D 0).rank) (z : Fin (Yc D 0).rank → EAf D), (∀ i, Matrix.mulVec (β⁻¹).val z i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → GlobalTheory.SeeConjChar.hT X h (pairAt X h PP a) z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D X h β hβ PP a z hz
  have hLf := GlobalTheory.KgFrame.Lf_eq D
  have hzL : z ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf := by
    rw [hLf]
    exact (hβ z).2 hz
  set S : Set (Fin (Yc D 0).rank → EAf D) := {v | v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf} with hS
  have h0 : (0 : Fin (Yc D 0).rank → EAf D) ∈ S := by
    show (0 : Fin (Yc D 0).rank → EAf D) ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf
    exact zero_mem _
  obtain ⟨hef, hz0, hbw⟩ := X.vectorsInLattice
  have he : ∀ a, e0T X h a ∈ S := GlobalTheory.SeeConjRead.cast_fun_mem_Lf h X.e0 (fun a => (hef a).1)
  have hf : ∀ a, f0T X h a ∈ S := GlobalTheory.SeeConjRead.cast_fun_mem_Lf h X.f0 (fun a => (hef a).2)
  have hb : ∀ a, bwT X h a ∈ S := GlobalTheory.SeeConjRead.cast_fun_mem_Lf h X.bw (fun a => (hbw a).1)
  have hbd : ∀ a, bwdT X h a ∈ S := GlobalTheory.SeeConjRead.cast_fun_mem_Lf h X.bwd (fun a => (hbw a).2)
  have hzz : z0T X h ∈ S := GlobalTheory.SeeConjRead.cast_mem_Lf h X.z0 hz0
  have hv : pairAt X h PP a ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf := by
    show pairAt X h PP a ∈ S
    unfold pairAt
    split_ifs
    · exact GlobalTheory.SeeConjRead.flagV_mem S h0 _ _ _ _ _ _ _ hf he hbd hzz a
    · exact GlobalTheory.SeeConjRead.flagV_mem S h0 _ _ _ _ _ _ _ hf he (fun i => hb _) hzz a
  unfold hT
  exact intAf_cast X h _ (Formalism.L2.SG.Pf.unitaryCongruence.hA_int _ (GlobalTheory.SeeConjRead.cast_mem_Lf h.symm _ hv)
    (GlobalTheory.SeeConjRead.cast_mem_Lf h.symm _ hzL))

end GlobalTheory.SeeConjChar
