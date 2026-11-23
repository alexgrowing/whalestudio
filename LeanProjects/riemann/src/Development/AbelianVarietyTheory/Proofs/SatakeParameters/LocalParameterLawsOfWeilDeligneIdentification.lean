import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DirectSumCancelRightStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharCompatibilitiesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParameterTensorOneDimInjectiveStatement

namespace GlobalTheory.RowLaws

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh GlobalTheory.RowTie

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem tie_unit (T : WDTie N A) (w : PlE H) :
    (T.e w (A.lpUnr w {1})).unr ∧ (T.e w (A.lpUnr w {1})).lpDim = 1 ∧
      (T.e w (A.lpUnr w {1})).frobEig = {1} := by
  obtain ⟨h1, h2, h3⟩ := A.lpUnr_spec w {1} (by simp)
  refine ⟨(T.unr w _).1 h1, ?_, ?_⟩
  · rw [T.dim, h3]; rfl
  · rw [← T.frobEig w _ h1, h2]

theorem paramLaws_of_tie (T : WDTie N A) : ParamLaws N A := by
  intro w
  refine ⟨fun a b χ h => (T.e w).injective ?_, fun χ h => (T.e w).injective ?_,
    fun a χ s h => (T.e w).injective ?_, fun a b χ h hab => ?_, fun a b c h => (T.e w).injective ?_⟩
  · rw [T.char _ _ _ h, T.sum, T.sum, T.char _ _ _ h, T.char _ _ _ h]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ _ _ 0).1
  · rw [T.char _ _ _ h, T.zero]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ (WD.lpZero _) (WD.lpZero _) _ 0).2.2.2.2.1
  · rw [T.char _ _ _ h, T.tw, T.tw, T.char _ _ _ h]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ (WD.lpZero _) _ s).2.1
  · apply (T.e w).injective
    have hχ : (T.e w χ).lpDim = 1 := by rw [T.dim, h]
    have := congrArg (T.e w) hab
    rw [T.char _ _ _ h, T.char _ _ _ h] at this
    exact GlobalTheory.T.weilDeligneParameter_tensor_oneDim_injective _ _ _ _ _ _ _ _ hχ this
  · have := congrArg (T.e w) h
    rw [T.sum, T.sum] at this
    exact GlobalTheory.T.directSum_cancel_right _ _ _ _ _ _ _ _ this

theorem cancel_of_tie (T : WDTie N A) : Cancel N A := fun w a b c h => (paramLaws_of_tie T w).2.2.2.2 a b c h

theorem charLaws_of_tie (T : WDTie N A) : CharLaws N A := by
  intro w a b χ χ' s h1 h2
  have h3 : A.lpDim (A.lpTw χ s) = 1 := by rw [A.lpDim_tw, h1]
  have h4 : A.lpDim (A.lpChar χ χ') = 1 := by rw [A.lpDim_char _ _ h2, h1]
  have h5 : A.lpDim (A.lpUnr w {1}) = 1 := (A.lpUnr_spec w {1} (by simp)).2.2
  refine ⟨(T.e w).injective ?_, (T.e w).injective ?_, (T.e w).injective ?_, (T.e w).injective ?_,
    (T.e w).injective ?_⟩
  · rw [T.char _ _ _ h1, T.sum, T.sum, T.char _ _ _ h1, T.char _ _ _ h1]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ _ _ 0).1
  · rw [T.char _ _ _ h1, T.tw, T.tw, T.char _ _ _ h1]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ (WD.lpZero _) _ s).2.1
  · rw [T.char _ _ _ h3, T.tw, T.tw, T.char _ _ _ h1]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ (WD.lpZero _) _ s).2.2.1
  · rw [T.char _ _ _ h2, T.char _ _ _ h1, T.char _ _ _ h4, T.char _ _ _ h2]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ _ _ 0).2.2.2.1
  · rw [T.char _ _ _ h5]
    obtain ⟨u1, u2, u3⟩ := tie_unit T w
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ (T.e w a) (WD.lpZero _) _ 0).2.2.2.2.2 u1 u2 u3

end GlobalTheory.RowLaws

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain in

theorem GlobalTheory.RowLaws.main : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    GlobalTheory.RowTie.WDTie N A → GlobalTheory.ThetaExh.ParamLaws N A ∧ GlobalTheory.RowTie.CharLaws N A ∧ GlobalTheory.RowTie.Cancel N A :=
  fun _ _ _ _ _ T => ⟨GlobalTheory.RowLaws.paramLaws_of_tie T, GlobalTheory.RowLaws.charLaws_of_tie T, GlobalTheory.RowLaws.cancel_of_tie T⟩
