import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ExpIndep

noncomputable section

open Polynomial

namespace UpperTheory.V.Z.Gam

def fac (c : ℂ) (t q : ℝ) (P : ℂ[X]) (s : ℂ) : ℂ :=
  c * Complex.exp (t * s) * P.eval ((q : ℂ) ^ (-s)) / P.eval ((q : ℂ) ^ (1 - s))

def PairG (L L' : ℂ → ℂ) (β : ℂ[X]) (q : ℝ) (P : ℂ[X]) : Prop :=
  ∃ (Z W A B : ℂ → ℂ) (k k' c₀ : ℂ) (t c : ℝ), Differentiable ℂ Z ∧ Differentiable ℂ W ∧ Z ≠ 0 ∧ k ≠ 0 ∧ k' ≠ 0 ∧
    (∀ s : ℂ, c < s.re → Z s = L s * A s ∧ W s = k * L (s + 1) * β.eval s * A s) ∧
    ∀ s : ℂ, s.re < -c → Z s = L' s * B s * fac c₀ t q P s ∧ W s = k' * L' (s + 1) * B s * fac c₀ t q P (s + 1)

def SecDiff : Prop :=
  ∀ (q : ℝ), 1 < q → ∀ (P P' : ℂ[X]) (c : ℂ), P.eval 0 = 1 → P'.eval 0 = 1 →
    P.comp (C (q : ℂ)⁻¹ * X) * P.comp (C (q : ℂ) * X) * P' ^ 2 =
      C c * (P'.comp (C (q : ℂ)⁻¹ * X) * P'.comp (C (q : ℂ) * X) * P ^ 2) → P = P'

def CrossG : Prop :=
  ∀ (L L' : ℂ → ℂ) (β β' : ℂ[X]) (q : ℝ) (P P' : ℂ[X]), 1 < q → β ≠ 0 → β' ≠ 0 → P.eval 0 = 1 → P'.eval 0 = 1 →
    PairG L L' β q P → PairG L L' β' q P' → P = P'

def PairGOps : Prop :=
  (∀ q : ℝ, PairG 1 1 1 q 1) ∧
  (∀ (L₁ L₁' L₂ L₂' : ℂ → ℂ) (β₁ β₂ : ℂ[X]) (q : ℝ) (P₁ P₂ : ℂ[X]), PairG L₁ L₁' β₁ q P₁ → PairG L₂ L₂' β₂ q P₂ →
    PairG (L₁ * L₂) (L₁' * L₂') (β₁ * β₂) q (P₁ * P₂)) ∧
  (∀ (L L' L₁ L₁' : ℂ → ℂ) (β : ℂ[X]) (q : ℝ) (P : ℂ[X]) (c : ℝ), PairG L L' β q P → (∀ s : ℂ, c < s.re → L s = L₁ s) →
    (∀ s : ℂ, s.re < -c → L' s = L₁' s) → PairG L₁ L₁' β q P) ∧
  ∀ (L L' : ℂ → ℂ) (β : ℂ[X]) (q : ℝ) (P : ℂ[X]) (z : ℂ), 1 < q → PairG L L' β q P →
    PairG (fun s => L (s - z)) (fun s => L' (s - z)) (β.comp (X - C z)) q (P.comp (C ((q : ℂ) ^ z) * X))

def CrossGOf : Prop := Inf.ExpAlg → Inf.ExpIndep → SecDiff → CrossG

end UpperTheory.V.Z.Gam
