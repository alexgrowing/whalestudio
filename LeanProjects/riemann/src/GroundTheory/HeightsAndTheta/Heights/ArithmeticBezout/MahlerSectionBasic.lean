import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Characterised
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LineInhabitant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

variable {n : ℕ}

def ballH (h : HermNorm n) : Set (Fin n → ℂ) := {v | h.norm v < 1}

def nrmv (h : HermNorm n) (v : Fin n → ℂ) : Fin n → ℂ := fun j => ((h.norm v : ℝ) : ℂ)⁻¹ * v j

def cycleSection (Z : ProjCycle ℂ n) (u : Fin n → ℂ) : ProjCycle ℂ n :=
  ∑ W ∈ Z.support, Z W • divCycle W u

def GreenSymmetry.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) (u u' : Fin n → ℂ),
    IsProjPrime W → (∃ g : MvPolynomial (Fin (e + 2) × Fin n) ℂ, IsChowForm W (e + 2) g) →
    linForm u ∉ W → linForm u' ∉ W → (∀ W' ∈ (divCycle W u).support, linForm u' ∉ W') →
      cycleIntegral h (divCycle W u) e (fsLog h u') + coneIntegral h W (e + 1) (fsLog h u) =
        cycleIntegral h (divCycle W u') e (fsLog h u) + coneIntegral h W (e + 1) (fsLog h u')

theorem GreenSymmetry.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      (∃ g : MvPolynomial (Fin (0 + 2) × Fin 2) ℂ, IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) (0 + 2) g) ∧
      linForm (fun j : Fin 2 => if j = 0 then (1 : ℂ) else 0) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      linForm (fun j : Fin 2 => if j = 1 then (1 : ℂ) else 0) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      (∀ W' ∈ (divCycle (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) (fun j : Fin 2 => if j = 0 then (1 : ℂ) else 0)).support,
        linForm (fun j : Fin 2 => if j = 1 then (1 : ℂ) else 0) ∉ W') := by
  have h0 : linForm (fun j : Fin 2 => if j = 0 then (1 : ℂ) else 0) = X 0 := by
    simp [linForm]
  have h1 : linForm (fun j : Fin 2 => if j = 1 then (1 : ℂ) else 0) = X 1 := by
    simp [linForm]
  refine ⟨LineChowForm.isProjPrime_line, ⟨LineChowForm.D2, LineChowForm.isChowForm_line⟩,
    LineChowForm.linForm_line, ?_, ?_⟩
  · rw [h1, Ideal.mem_bot]; exact X_ne_zero _
  · intro W' hW' hX1
    rw [h1] at hX1
    have hmem : W' ∈ relComps ((⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ⊔
        Ideal.span {linForm (fun j : Fin 2 => if j = 0 then (1 : ℂ) else 0)}) := by
      by_contra hc
      apply Finsupp.mem_support_iff.mp hW'
      simp only [divCycle, fundCycle, Finsupp.onFinset_apply]
      exact if_neg hc
    obtain ⟨hmin, j, hj⟩ := hmem
    have hX0 : X 0 ∈ W' := by
      apply hmin.1.2
      rw [h0]
      exact Ideal.mem_sup_right (Ideal.subset_span rfl)
    fin_cases j
    · exact hj hX0
    · exact hj hX1

end

end GroundTheory.Heights₂.Heights
