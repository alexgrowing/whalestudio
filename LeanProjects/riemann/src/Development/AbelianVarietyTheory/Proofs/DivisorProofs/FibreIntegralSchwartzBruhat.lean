import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarOIsAddHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DropColsInsB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeptColNeLastCol
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatConvolutionLocalFieldPower
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.StdPairLoc GlobalTheory.ColIns GlobalTheory.ColFib
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

noncomputable section

namespace GlobalTheory.ColFib

variable {F : Type} [Field F] [NumberField F]

theorem continuous_insB_zero (v : Pl F) (a b : ℕ) :
    Continuous fun C : Matrix (Fin a) (Fin (a + b)) (Fv F v) => insB C 0 := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [insB]
  split_ifs <;> fun_prop

theorem continuous_dropCols (v : Pl F) (a b : ℕ) :
    Continuous fun X : Matrix (Fin a) (Fin (a + (b + 2))) (Fv F v) => dropCols X :=
  continuous_pi fun i => continuous_pi fun j => by simp only [dropCols]; fun_prop

theorem fibInt_mem_SB (F : Type) [Field F] [NumberField F] (v : Pl F) (a b : ℕ)
    (Φ : Matrix (Fin a) (Fin (a + (b + 2))) (Fv F v) → ℂ)
    (hΦ : Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + (b + 2))) (Fv F v))) :
    fibInt v Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) (Fv F v)) := by
  have hΦ' : Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin a) (Fin (a + (b + 2))) (Fv F v)) := by
    rw [← GlobalTheory.WeilM.SB_eq]; exact hΦ
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro Y
    have hc : Continuous fun Y' : Matrix (Fin a) (Fin (a + b)) (Fv F v) => -insB (Y' - Y) (0 : Fin a → Fv F v) :=
      ((continuous_insB_zero v a b).comp (continuous_sub_right Y)).neg
    have ht : Filter.Tendsto (fun Y' : Matrix (Fin a) (Fin (a + b)) (Fv F v) => -insB (Y' - Y) (0 : Fin a → Fv F v))
        (nhds Y) (nhds 0) := by
      have h := hc.tendsto Y
      have e : -insB (Y - Y) (0 : Fin a → Fv F v) = 0 := by
        rw [sub_self]; funext i j; simp [insB]
      rwa [e] at h
    filter_upwards [ht.eventually (GlobalTheory.SBConv.eventually_translate hΦ')] with Y' hY'
    unfold fibInt
    congr 1
    funext t
    have e : insB Y' t = insB Y t - -insB (Y' - Y) (0 : Fin a → Fv F v) := by
      rw [sub_neg_eq_add, ← insB_add, add_sub_cancel, add_zero]
    rw [e, hY']
  · refine HasCompactSupport.intro ((hΦ.2.isCompact).image (continuous_dropCols v a b)) fun Y hY => ?_
    unfold fibInt
    have h0 : (fun t => Φ (insB Y t)) = fun _ => (0 : ℂ) := by
      funext t
      refine image_eq_zero_of_notMem_tsupport fun hm => hY ⟨_, hm, ?_⟩
      exact dropCols_insB Y t
    rw [h0, integral_zero]

end GlobalTheory.ColFib

end

example : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (a b : ℕ) (Φ : Matrix (Fin a) (Fin (a + (b + 2))) (Fv F v) → ℂ), Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + (b + 2))) (Fv F v)) → fibInt v Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) (Fv F v)) := GlobalTheory.ColFib.fibInt_mem_SB
