import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFunctionalRestrict

noncomputable section

open scoped SchwartzMap

namespace PositivityTheory.SiegelWeilFormula.KFock

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def reidxCLE {α β : Type} (e : α ≃ β) : (β → V) ≃L[ℝ] (α → V) where
  toFun y a := y (e a)
  invFun x b := x (e.symm b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv y := funext fun b => by simp
  right_inv x := funext fun a => by simp
  continuous_toFun := continuous_pi fun a => continuous_apply (e a)
  continuous_invFun := continuous_pi fun b => continuous_apply (e.symm b)

def optCLE (α : Type) : (Option α → V) ≃L[ℝ] V × (α → V) where
  toFun y := (y none, fun a => y (some a))
  invFun p o := Option.elim o p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv y := funext fun o => by cases o <;> rfl
  right_inv p := rfl
  continuous_toFun := (continuous_apply none).prodMk (continuous_pi fun a => continuous_apply (some a))
  continuous_invFun := continuous_pi fun o => by
    cases o with
    | none => exact continuous_fst
    | some a => exact (continuous_apply a).comp continuous_snd

def oneSch : 𝓢(PEmpty → V, ℂ) where
  toFun _ := 1
  smooth' := contDiff_const
  decay' k n := ⟨1, fun x => by
    have hx : ‖x‖ = 0 := by rw [Subsingleton.elim x 0, norm_zero]
    refine mul_le_one₀ ?_ (norm_nonneg _) ?_
    · rw [hx]; exact pow_le_one₀ le_rfl zero_le_one
    · cases n with
      | zero => rw [norm_iteratedFDeriv_zero]; simp
      | succ n => rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]; simp⟩

variable (V) in

def PS (α : Type) [Fintype α] : Prop := ∀ S : α → 𝓢(V, ℂ), ∃ T : 𝓢(α → V, ℂ), ∀ y, T y = ∏ w, S w (y w)

theorem piProdSch' (W : Type) [Fintype W] (S : W → 𝓢(V, ℂ)) :
    ∃ T : 𝓢(W → V, ℂ), ∀ y, T y = ∏ w, S w (y w) := by
  revert S
  change PositivityTheory.SiegelWeilFormula.KFock.PS V W
  refine Fintype.induction_empty_option (P := fun α (_ : Fintype α) => PositivityTheory.SiegelWeilFormula.KFock.PS V α)
    ?_ ?_ ?_ W
  · intro α β _ e hα S
    letI : Fintype α := Fintype.ofEquiv β e.symm
    obtain ⟨T, hT⟩ := hα (fun a => S (e a))
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (PositivityTheory.SiegelWeilFormula.KFock.reidxCLE e) T,
      fun y => ?_⟩
    rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hT]
    exact Fintype.prod_equiv e _ _ (fun a => rfl)
  · intro S
    refine ⟨PositivityTheory.SiegelWeilFormula.KFock.oneSch, fun y => ?_⟩
    show (1 : ℂ) = _
    rw [Finset.univ_eq_empty, Finset.prod_empty]
  · intro α _ hα S
    obtain ⟨T₀, hT₀⟩ := hα (fun a => S (some a))
    obtain ⟨f, hf⟩ := GlobalTheory.SchwartzHadamard.exists_schwartz_prod (S none) T₀
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (PositivityTheory.SiegelWeilFormula.KFock.optCLE α) f,
      fun y => ?_⟩
    rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hf, Fintype.prod_option]
    show S none (y none) * T₀ (fun a => y (some a)) = _
    rw [hT₀]

end PositivityTheory.SiegelWeilFormula.KFock

end
