import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZeroMemSolSet
import Formalism.UnipotentAdelicQuotients.EllRegCheck
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DwSmoothLocalLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AestronglyMeasurableExtendByZeroOffSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticSystemDerivativeContinuousFunctionalStatement
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction

noncomputable section

namespace GlobalTheory.HCA.SupEst

variable {d : ℕ}

theorem dw_zero_fun : ∀ w : List (Fin d), dw w (fun _ : E d => (0 : ℂ)) = fun _ => 0
  | [] => rfl
  | j :: w => by
      funext x
      show fderiv ℝ (dw w (fun _ : E d => (0 : ℂ))) x (ev j) = 0
      rw [dw_zero_fun w]
      simp

theorem tr_eq_zero_of_notMem {ι : Type} (P : Sys d ι) (i : ι) {φ : E d → ℂ} {x : E d}
    (hx : x ∉ tsupport φ) : P.tr i φ x = 0 := by
  unfold Sys.tr trOp
  refine Finset.sum_eq_zero fun n _ => Finset.sum_eq_zero fun w _ => ?_
  have hO : IsOpen (tsupport φ)ᶜ := (isClosed_tsupport φ).isOpen_compl
  have hEq : Set.EqOn (fun y => P.a i n w y * φ y) (fun _ => (0 : ℂ)) (tsupport φ)ᶜ := by
    intro y hy
    have : φ y = 0 := image_eq_zero_of_notMem_tsupport hy
    simp [this]
  have := eqOn_dw_of_isOpen hO (List.ofFn w) _ _ hEq hx
  rw [this, dw_zero_fun]
  simp

end GlobalTheory.HCA.SupEst

open GlobalTheory.HCA.SupEst in

theorem GlobalTheory.HCA.dw_le_sup : ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)), IsOpen U → (∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) → (∀ x ∈ U, ∀ ξ : E d, ξ ≠ 0 → ∃ i, P.symb i x ξ ≠ 0) → ∀ (w : List (Fin d)), ∀ x₀ ∈ U, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : E d → ℂ, ContinuousOn u U → WeakSol P U u → ∀ M : ℝ, (∀ x ∈ U, ‖u x‖ ≤ M) → ‖dw w u x₀‖ ≤ C * M := by
  intro d ι _ P U hU ha hell w x₀ hx₀
  obtain ⟨S, hS⟩ := (solSet_closed_submodule d ι P U hU ha).2
  obtain ⟨l, hl⟩ := GlobalTheory.T.ellipticSystem_derivative_continuous_functional d ι P U hU ha hell S hS w x₀ hx₀
  refine ⟨‖l‖, norm_nonneg _, ?_⟩
  intro u hu hweak M hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x₀ hx₀)
  have hcont : Continuous (U.restrict u) := continuousOn_iff_continuous_restrict.mp hu
  let u' : U →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup (U.restrict u) hcont M
    (fun x => hM x.1 x.2)
  have hu'n : ‖u'‖ ≤ M := BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hM0 _
  have hext : Set.EqOn (ext0 U u') u U := by
    intro x hx
    simp only [ext0, hx, dif_pos, u']
    rfl
  have hmem : u' ∈ solSet P U := by
    intro i φ h1 h2 h3
    rw [← hweak i φ h1 h2 h3]
    congr 1
    funext x
    by_cases hx : x ∈ U
    · rw [hext hx]
    · have : x ∉ tsupport φ := fun h => hx (h3 h)
      rw [tr_eq_zero_of_notMem P i this]
      simp
  have hmemS : u' ∈ S := by rw [← SetLike.mem_coe, hS]; exact hmem
  have hval : l ⟨u', hmemS⟩ = dw w u x₀ := by
    rw [hl]
    exact eqOn_dw_of_isOpen hU w _ _ hext hx₀
  rw [← hval]
  calc ‖l ⟨u', hmemS⟩‖ ≤ ‖l‖ * ‖(⟨u', hmemS⟩ : S)‖ := l.le_opNorm _
    _ = ‖l‖ * ‖u'‖ := rfl
    _ ≤ ‖l‖ * M := mul_le_mul_of_nonneg_left hu'n (norm_nonneg _)

end
