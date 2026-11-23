import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

variable {n : ℕ}

def fsLogReg (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) (y : Fin n → ℂ) : ℝ :=
  Real.log ((‖∑ j, u j * y j‖ ^ 2 + ε * h.dualNorm y ^ 2) / h.dualNorm y ^ 2) / 2

open Classical in

def formInt (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) (e : ℕ)
    (a b : (Fin n → ℂ) → ℝ) : ℝ :=
  if hℓ : ∃ ℓ : Fin n → ℂ, linForm ℓ ∉ W then
    varInt (W ⊔ Ideal.span {linForm hℓ.choose - 1}) (e + 1) a
      (vecCons b fun _ x => Real.log (h.dualNorm x))
  else 0

theorem fsLogReg_tendsto (h : HermNorm n) (u y : Fin n → ℂ) (hy : 0 < h.dualNorm y)
    (hu : ∑ j, u j * y j ≠ 0) :
    Tendsto (fun ε => fsLogReg h u ε y) (𝓝 0) (𝓝 (fsLog h u y)) := by
  have hc : (0 : ℝ) < h.dualNorm y ^ 2 := by positivity
  have hs : (0 : ℝ) < ‖∑ j, u j * y j‖ := norm_pos_iff.mpr hu
  have hcont : ContinuousAt (fun ε : ℝ =>
      Real.log ((‖∑ j, u j * y j‖ ^ 2 + ε * h.dualNorm y ^ 2) / h.dualNorm y ^ 2) / 2) 0 := by
    refine ContinuousAt.div_const (ContinuousAt.log ?_ ?_) _
    · fun_prop
    · simp only [zero_mul, add_zero]
      positivity
  have := hcont.tendsto
  simp only [zero_mul, add_zero] at this
  unfold fsLogReg
  convert this using 2
  rw [fsLog, ← div_pow, Real.log_pow]
  push_cast
  ring

def FormIntSymm.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) (u u' : Fin n → ℂ) (ε δ : ℝ),
    IsProjPrime W → (∃ g : MvPolynomial (Fin (e + 2) × Fin n) ℂ, IsChowForm W (e + 2) g) →
    0 < ε → 0 < δ →
      formInt h W e (fsLogReg h u δ) (fsLogReg h u' ε) =
        formInt h W e (fsLogReg h u' ε) (fsLogReg h u δ)

def FormIntPos.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) (u u' : Fin n → ℂ)
    (ε δ δ' : ℝ),
    IsProjPrime W → (∃ g : MvPolynomial (Fin (e + 2) × Fin n) ℂ, IsChowForm W (e + 2) g) →
    0 < ε → 0 < δ → δ ≤ δ' →
      formInt h W e (fsLogReg h u δ) (fsLogReg h u' ε) + coneIntegral h W (e + 1) (fsLogReg h u δ) ≤
        formInt h W e (fsLogReg h u δ') (fsLogReg h u' ε) +
          coneIntegral h W (e + 1) (fsLogReg h u δ')

def FormIntLelong.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) (u u' : Fin n → ℂ) (δ : ℝ),
    IsProjPrime W → (∃ g : MvPolynomial (Fin (e + 2) × Fin n) ℂ, IsChowForm W (e + 2) g) →
    linForm u' ∉ W → 0 < δ →
      Tendsto (fun ε => formInt h W e (fsLogReg h u δ) (fsLogReg h u' ε)) (𝓝[>] 0)
        (𝓝 (cycleIntegral h (divCycle W u') e (fsLogReg h u δ) -
          coneIntegral h W (e + 1) (fsLogReg h u δ)))

def RegConeLimit.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    IsProjPrime J → (∃ g : MvPolynomial (Fin (e + 1) × Fin n) ℂ, IsChowForm J (e + 1) g) →
    linForm u ∉ J →
      Tendsto (fun ε => coneIntegral h J e (fsLogReg h u ε)) (𝓝[>] 0)
        (𝓝 (coneIntegral h J e (fsLog h u)))

end

end GroundTheory.Heights₂.Heights
