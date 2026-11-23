import Formalism.PeriodIntegrals.LatDefs

noncomputable section

open Classical

namespace PI.ThetaNormCM

def hf1 (Λ : AddSubgroup ℂ) (z w : ℂ) : ℂ := z * (starRingEnd ℂ) w / (PI.area Λ : ℂ)

def al1 (d : ℕ) (Λ : AddSubgroup ℂ) (x : ℂ) : ℂ := (-1 : ℂ) ^ (round (Real.sqrt d / 2 * (hf1 Λ x x).re))

def IsTheta0 (d : ℕ) (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : Prop :=
  Differentiable ℂ G ∧ (∀ x ∈ Λ, ∀ z, al1 d Λ x * PI.U1 Λ x G z = G z) ∧ G 0 = 1

def normSq1 (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : ℝ :=
  let Fd : Set ℂ := Classical.epsilon (fun Fd => MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume)
  ⨍ z in Fd, ‖G z‖ ^ 2 * Real.exp (-Real.pi * (hf1 Λ z z).re)

def IsTwoTorsionPointUnkilled (d : ℕ) (Λ : AddSubgroup ℂ) (t : ℂ) : Prop :=
  2 * t ∈ Λ ∧ ((1 + Complex.I * (Real.sqrt d : ℂ)) / 2) * t ∉ Λ ∧
    ((1 - Complex.I * (Real.sqrt d : ℂ)) / 2) * t ∉ Λ

end PI.ThetaNormCM

namespace PI

open PI.ThetaNormCM in

def ThetaNormCM : Prop :=
  ∀ d : ℕ, Squarefree d → d % 8 = 7 →
    ∀ (ω₁ τ : ℂ), ω₁ ≠ 0 → 0 < τ.im →
    (∀ x ∈ AddSubgroup.closure ({ω₁, ω₁ * τ} : Set ℂ),
      ((1 + Complex.I * (Real.sqrt d : ℂ)) / 2) * x ∈ AddSubgroup.closure ({ω₁, ω₁ * τ} : Set ℂ)) →
    ∀ a b : ℕ, a ≤ 1 → b ≤ 1 →
    IsTwoTorsionPointUnkilled d (AddSubgroup.closure {ω₁, ω₁ * τ}) (ω₁ * ((1 - (a : ℂ)) * τ + (1 - (b : ℂ))) / 2) →
    ∀ G, IsTheta0 d (AddSubgroup.closure {ω₁, ω₁ * τ}) G →
      (normSq1 (AddSubgroup.closure {ω₁, ω₁ * τ}) G)⁻¹ = Real.sqrt (2 * τ.im) *
        (Real.exp (-Real.pi * (a : ℝ) ^ 2 * τ.im / 4) * ‖jacobiTheta₂ (((a : ℂ) * τ + (b : ℂ)) / 2) τ‖) ^ 2

end PI
