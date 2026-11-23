import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OtherInstanceCharacterEqPsiSymmetricArgument
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf

namespace GlobalTheory.Mem.SymChar.ZPair
open GlobalTheory.Mem.SymFrame

theorem rank_eq' (D : D7) : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
  unfold Ranks.r Ranks.rS
  obtain ⟨t, ht⟩ := D.R.m_even
  have := D.R.two_le_m
  omega

theorem zmod_hA_z0_symVec (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (j : Fin D.R.r) :
    ZMod' X.B.I X.B.g (hA X.B.I X.z0 (symVec X w j) - (if j.val = D.R.rS + D.R.k then -1 else 0)) := by
  have hr := rank_eq' D
  have hj := j.2
  unfold symVec GlobalTheory.SeeConjRead.flagV epsW
  split_ifs
  · exfalso; omega
  · rw [sub_zero, unitaryCongruence.hA_symm]; exact unitaryCongruence.Z_sig _ _ (X.formsAtZero.2 _).1
  · exfalso; omega
  · rw [sub_zero]; exact (X.weightVectorsIntegral _).1
  · exfalso; omega
  · rw [sub_zero]; exact (X.weightVectorsIntegral _).2.1
  · rw [sub_neg_eq_add]; exact X.formsAtZero.1
  · rw [sub_zero, unitaryCongruence.hA_symm]; exact unitaryCongruence.Z_sig _ _ (X.formsAtZero.2 _).2
  · exfalso; omega

theorem hA_z0_symVec : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (j : Fin D.R.r), hA X.B.I X.z0 (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) j) - (if j.val = D.R.rS + D.R.k then -1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  intro D X kv hg j
  exact GlobalTheory.Mem.SymChar.wInt_of_zmod X kv.1 hg (zmod_hA_z0_symVec D X _ j)

end GlobalTheory.Mem.SymChar.ZPair
