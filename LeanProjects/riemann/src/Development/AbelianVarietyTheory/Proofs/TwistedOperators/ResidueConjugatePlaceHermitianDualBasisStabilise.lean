import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CPAsIdeal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairTable
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SurjectiveReductionOntoFiniteLevelGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjChar

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf

theorem cpt_cP_eq_zero_of_orth {D : D7} {PP : Pl D.host.E} {e : EAf D} (ho : e * GlobalTheory.StdFrames.sg D e = 0)
    (h1 : GlobalTheory.StdFrames.cpt PP e = 1) : GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP PP) e = 0 := by
  have h2 := GlobalTheory.StdFrames.cpt_sg_eq_zero (Q := GlobalTheory.IdemSupport.cP PP) (z := 1 - e)
    (by rw [GlobalTheory.StdFrames.cP_cP, RingHom.map_sub, h1, RingHom.map_one, sub_self])
  rw [RingHom.map_sub, RingHom.map_one, RingHom.map_sub, RingHom.map_one, sub_eq_zero] at h2
  have h3 := congrArg (GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP PP)) ho
  rwa [RingHom.map_mul, ← h2, mul_one, RingHom.map_zero] at h3

theorem resT_eq_zero_of_fixed {D : D7} {Q : Pl D.host.E} {e x : EAf D} (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (he : GlobalTheory.StdFrames.cpt Q e = 0) (hf : x = e * x) : resT Q x = 0 := by
  unfold resT
  rw [dif_pos hx]
  refine (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt Q ⟨x, hx⟩).2 ?_
  have h0 : GlobalTheory.StdFrames.cpt Q x = 0 := by rw [hf, RingHom.map_mul, he, zero_mul]
  show Valued.v (GlobalTheory.StdFrames.cpt Q x) < 1
  rw [h0, Valuation.map_zero]
  exact zero_lt_one

theorem resT_cP_hT_bwd_eq_zero : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ PP : Pl D.host.E, GlobalTheory.SeeConjChar.sideAt X h PP = true → ∀ M ∈ St β, ∀ i j : Fin D.R.k, GlobalTheory.SeeConjChar.hT X h (bwdT X h i) (Matrix.mulVec M.val (bwT X h j)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.hT X h (bwdT X h i) (Matrix.mulVec M.val (bwT X h j))) = 0 := by
  intro D X h β hF PP hs M hM i j
  have hb := X.vectorsInLattice.2.2
  have ho := X.ew_orth
  have hw := X.bwd_w i
  have h1 : GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 := by
    unfold sideAt at hs
    simpa only [decide_eq_true_eq] using hs
  have hfix : ∀ v, hA X.B.I (X.bwd i) v = X.ew * hA X.B.I (X.bwd i) v := fun v => by
    conv_lhs => rw [hw, unitaryCongruence.hA_smul_left, unitaryCongruence.sigA_sigA]
  obtain ⟨⟨I⟩⟩ := X
  dsimp only at h hb ho hfix
  subst h
  have hv := (hb j).1
  rw [GlobalTheory.SeeMatchOnto.Lf_eq] at hv
  have hv2 := (GlobalTheory.SeeMatchOnto.mem_hatL_iff_of_St hF hM _).1 hv
  have hv3 := (GlobalTheory.SeeMatchOnto.Lf_eq (D := D)).ge hv2
  have hint := unitaryCongruence.hA_int _ (hb i).2 hv3
  exact ⟨hint, resT_eq_zero_of_fixed hint (cpt_cP_eq_zero_of_orth ho h1) (hfix _)⟩

end GlobalTheory.SeeConjChar
