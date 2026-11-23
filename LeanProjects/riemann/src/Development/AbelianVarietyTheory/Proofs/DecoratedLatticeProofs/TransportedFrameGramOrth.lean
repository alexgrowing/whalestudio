import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.I0M
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfGluingFacts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem transported_frame_gram_orth : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀) (i j : Fin (D.sp.X 0).rank) (a : Fin D.R.rS), (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) j)) = (D.sp.X 0).gram i j ∧ (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (X.eX a) = 0 ∧ (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (X.fY a) = 0 ∧ (VS D).hT (X.zu u) (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) = 0 := by
  intro D X u F₀ tr i j a
  have key : ∀ (x y : (VS D).V), (VS D).hT (tr.wt.symm x) (tr.wt.symm y) = (VS D).hT x y := by
    intro x y
    rw [← tr.wt_isom, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have key2 : ∀ (x y : (VS D).V), (VS D).hT (tr.wt.symm x) y = (VS D).hT x (tr.wt y) := by
    intro x y
    rw [← tr.wt_isom, LinearEquiv.apply_symm_apply]
  have key3 : ∀ (x y : (VS D).V), (VS D).hT x (tr.wt.symm y) = (VS D).hT (tr.wt x) y := by
    intro x y
    rw [← tr.wt_isom, LinearEquiv.apply_symm_apply]
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Formalism.L2.SG.ColDict.qFr, Formalism.L2.SG.ColDict.xFr, key, Fin.cast_cast, Fin.cast_eq_self]
    exact D.sp.iXY_isom 0 hm _ _
  · simp only [Formalism.L2.SG.ColDict.qFr, Formalism.L2.SG.ColDict.xFr, key2, tr.wt_e]
    exact (D.sp.hyp_orthX a _).1
  · simp only [Formalism.L2.SG.ColDict.qFr, Formalism.L2.SG.ColDict.xFr, key2, tr.wt_f]
    exact (D.sp.hyp_orthX a _).2
  · simp only [Formalism.L2.SG.ColDict.qFr, Formalism.L2.SG.ColDict.xFr, key3, tr.weight_z]
    exact Formalism.MainNotions.BridgeLemma₂.z_orth_embedding D u _

end GlobalTheory.Core.Mi
