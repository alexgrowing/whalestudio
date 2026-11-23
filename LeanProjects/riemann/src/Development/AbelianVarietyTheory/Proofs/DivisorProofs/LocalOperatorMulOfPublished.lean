import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement

noncomputable section

namespace GlobalTheory.ThK.LemF

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem locOpMul_of_actsEx (hA : ActsEx) : LocOpMul := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair v x y hx1 hx2 hy1 hy2 φ hφ
  have hy : Acts (evFin F v) (om y) φ (locOp v (om y) φ) := acts_locOp_om hA hPair hy1 hy2 hφ
  have hφ' := locOp_mem v (om y) φ
  have hx : Acts (evFin F v) (om x) (locOp v (om y) φ) (locOp v (om x) (locOp v (om y) φ)) :=
    acts_locOp_om hA hPair hx1 hx2 hφ'
  have hpres := (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hPair.weil).pres
  refine locOp_eq hφ (locOp_mem v _ _) fun ρ hρ => ?_
  have hρ' : Rest (evFin F v) (locOp v (om y) φ) ρ := ⟨hρ.1, by rw [← hy ρ hρ]; exact hpres y _ hρ.2⟩
  rw [map_mul, Module.End.mul_apply, hy ρ hρ, hx ρ hρ']

theorem locOpMul (hP : GlobalTheory.FunPr.Hypotheses₂) : LocOpMul := locOpMul_of_actsEx (GlobalTheory.T.theta_action_exists hP)

end GlobalTheory.ThK.LemF

end
