import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneSubEwMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymChar.Resid

theorem hA_bwd_symVec : ∀ (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (k : Fin 2), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → GlobalTheory.Mem.SymFrame.EwAt X w → 1 - X.ew ∈ GlobalTheory.Mem.SymChar.wInt X w → ∀ (i : Fin D.R.k) (j : Fin D.R.r), hA X.B.I (X.bwd i) (GlobalTheory.Mem.SymFrame.symVec X w j) - (if j = GlobalTheory.Mem.SymChar.Resid.posB D i then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X w := by
  intro D X w k hg hw hew i j
  have hZ : ∀ {c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F}, ZMod' X.B.I X.B.g c → c ∈ wInt X w :=
    fun hc => wInt_of_zmod X k hg hc
  have he : GlobalTheory.Mem.SymFrame.epsW X w = X.bw := by
    unfold GlobalTheory.Mem.SymFrame.epsW; rw [if_pos hw]
  have hr := rank_eq D
  have hp : (j = posB D i) ↔ j.1 = D.R.rS + i.1 := by rw [Fin.ext_iff]; rfl
  have hi := i.2
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV
  rw [he]
  by_cases h1 : j.1 < D.R.rS
  · rw [dif_pos h1, if_neg (by rw [hp]; omega), sub_zero]
    apply hZ
    rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]
    exact Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I X.B.g ((X.weightVectorsIntegral i).2.2 _).2.2.1
  rw [dif_neg h1]
  by_cases h2 : j.1 < D.R.rS + D.R.k
  · rw [dif_pos h2]
    have hd := X.bw_dual i ⟨j.1 - D.R.rS, by omega⟩
    by_cases hl : j.1 = D.R.rS + i.1
    · rw [if_pos (hp.2 hl)]
      rw [if_pos (Fin.ext (by simp only; omega))] at hd
      have := sub_mem (hZ hd) hew
      convert this using 1
      ring
    · rw [if_neg (fun h => hl (hp.1 h))]
      rw [if_neg (fun h => hl (by have := congrArg Fin.val h; simp only at this; omega))] at hd
      simpa using hZ hd
  rw [dif_neg h2]
  by_cases h4 : j.1 = D.R.rS + D.R.k
  · rw [dif_pos h4, if_neg (by rw [hp]; omega), sub_zero]
    apply hZ
    rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]
    exact Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I X.B.g (X.weightVectorsIntegral i).2.1
  rw [dif_neg h4]
  by_cases h3 : j.1 < 2 * D.R.rS + D.R.k + 1
  · rw [dif_pos h3, if_neg (by rw [hp]; omega), sub_zero]
    apply hZ
    rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]
    exact Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I X.B.g ((X.weightVectorsIntegral i).2.2 _).2.2.2
  · rw [dif_neg h3, if_neg (by rw [hp]; omega), sub_zero, hA_zero_right']
    exact zero_mem _

end GlobalTheory.Mem.SymChar.Resid
