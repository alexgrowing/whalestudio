import Mathlib
import Formalism.WeightedDeltaMeans.LowerBoundLinearPower

open Finset

noncomputable section

namespace Formalism.ShimuraLimitIdentity

def MeanOfSlopes : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (sl volc Pc : ι → ℝ) (D degu P vol : ℝ),
    0 ≤ D → 0 < degu → (∀ c, 0 < volc c) → (∀ c c', volc c = volc c') →
    (∀ c, sl c = Pc c / ((D + 1) * (volc c * degu))) →
    P = (∑ c, Pc c) → vol = (∑ c, volc c) →
    (∑ c, sl c) / (Fintype.card ι : ℝ) = P / ((D + 1) * (vol * degu))

def MeanWeighted : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (sl volc Pc : ι → ℝ) (D degu P vol : ℝ),
    0 ≤ D → 0 < degu → (∀ c, 0 < volc c) →
    (∀ c, sl c = Pc c / ((D + 1) * (volc c * degu))) →
    P = (∑ c, Pc c) → vol = (∑ c, volc c) →
    (∑ c, volc c * sl c) / vol = P / ((D + 1) * (vol * degu))

def SecondTermBound : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] (N j : ℕ), 0 < N → j ≤ N →
    ∀ (u : Ψ → Fin N → ℝ), (∀ τ, Antitone (u τ)) →
    ∀ (A0 b0 : Ψ → ℝ) (D L vhFl rest P Λ K1 K2 K5 spread : ℝ),
      0 ≤ D → 0 < L → 0 ≤ vhFl → 0 ≤ Λ → 0 ≤ K1 → 0 ≤ K2 →
      P = vhFl + (D + 1) * L *
          (∑ τ, (A0 τ * (∑ i ∈ top N j, u τ i) + b0 τ * (∑ i : Fin N, u τ i))) + rest →
      (∀ τ, |(j : ℝ) * A0 τ + (N : ℝ) * b0 τ| ≤ K1 * N * Λ) →
      (∀ τ, -(K2 * Λ) ≤ A0 τ) →
      |rest| ≤ K5 * ((D + 1) * L * spread) →
      -((D + 1) * L * ((K1 + K2) * Λ * (∑ τ, ∑ i, |u τ i|) + K5 * spread)) ≤ P

def LowerBoundAtBase : Prop :=
  ∀ (B0 r0 tail A0 : ℝ) (bad : Finset ℕ), 2 ≤ B0 → (∀ p ∈ bad, p.Prime) →
    (bad.card : ℝ) ≤ B0 → 0 ≤ tail →
    A0 = r0 - 1 / 2
        - (∑ p ∈ (Finset.range (⌊B0⌋₊ + 1)).filter Nat.Prime ∪ bad,
            (p : ℝ) * Real.log p / ((p : ℝ) ^ 2 - 1)) + tail →
    r0 - 1 / 2 - 20 * Real.log B0 ≤ A0 ∧
    ∀ rd Lchi : ℝ, 1 ≤ rd → 0 ≤ Lchi →
      -((20 + 2 * |r0 - 1 / 2|) * (Real.log (B0 * rd) + Lchi)) ≤ A0

def SpreadBound : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] (N j' : ℕ) (u : Ψ → Fin N → ℝ) (nodes : Ψ → Finset (Fin N))
    (osc : Ψ → ℝ) (Cn : ℝ), 0 ≤ Cn → (∀ τ, 0 ≤ osc τ) → (∀ τ, j' ≤ (nodes τ).card) →
    (∀ τ, ∀ i ∈ nodes τ, osc τ ≤ Cn * |u τ i|) →
    (j' : ℝ) * (∑ τ, osc τ) ≤ Cn * (∑ τ, ∑ i, |u τ i|)

def SpreadFails : Prop :=
  ¬ ∃ C : ℝ, ∀ (N j' : ℕ) (u : Fin N → ℝ), 2 * j' ≤ N → Antitone u →
    ∀ a b : Fin N, (j' : ℝ) * (u a - u b) ≤ C * (∑ i, |u i|)

def LogBaseHeightBound : Prop :=
  ∀ (f N H b h0 B0 : ℝ), 1 ≤ f → 1 ≤ N → 0 ≤ H → H ≤ 8 * b / h0 → 8 ≤ h0 → 4 * f * N ^ 2 ≤ b →
    2 ≤ b → B0 = 4 * f * N ^ 2 * (1 + H) →
    4 ≤ B0 ∧ Real.log B0 ≤ 3 * Real.log b

def NefAtBaseHeight : Prop :=
  ∀ (f N M g B0 : ℝ), 1 ≤ f → 1 ≤ N → 0 ≤ M → 0 < g → B0 = 4 * f * N ^ 2 * (1 + M / g) →
    4 * f * N ^ 2 * M + g ≤ (B0 - 2) * g

def SlopeExport : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (sl volc Pc : ι → ℝ)
    (DY degu P vol Ct K5 Cs CB B0 spread Up : ℝ)
    (T U U1 PP b rd Lchi llx x LL0 X Ca e1 : ℝ),

    0 ≤ DY → 0 < degu → (∀ c, 0 < volc c) → (∀ c c', volc c = volc c') →
    (∀ c, sl c = Pc c / ((DY + 1) * (volc c * degu))) →
    P = (∑ c, Pc c) → vol = (∑ c, volc c) →

    -((DY + 1) * (vol * degu) * (Ct * (Real.log (B0 * rd) + Lchi) * Up + K5 * spread)) ≤ P →
    0 ≤ Ct → 0 ≤ K5 →

    0 ≤ Cs → spread ≤ Cs * Up → 1 ≤ B0 → Real.log B0 ≤ CB * Real.log b → 1 ≤ CB →
    0 ≤ T → (T + DY + 1) * U1 ≤ U + PP → 0 ≤ Up → Up ≤ U1 →

    Real.exp 1 ≤ b → 1 ≤ rd → 0 ≤ Lchi → 1 ≤ llx → 1 ≤ x →
    LL0 = Real.log (b * rd) * llx + Lchi + Real.log x →
    Ca = Ct * CB + K5 * Cs → X = Ca * LL0 * Up → e1 = Ca * LL0 * PP →
    0 ≤ X ∧ -X ≤ (∑ c, sl c) / (Fintype.card ι : ℝ) ∧ T * X ≤ Ca * LL0 * U + e1

def SlopeFull : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (Ψ : Type) [Fintype Ψ] (N j : ℕ), 0 < N → j ≤ N →
    ∀ (u' : Ψ → Fin N → ℝ), (∀ τ, Antitone (u' τ)) →
    ∀ (sl volc Pc : ι → ℝ) (A0 b0 : Ψ → ℝ)
      (DY degu P vol hFl rest K1 K2 K5 Cs CB B0 spread : ℝ)
      (T U U1 PP b rd Lchi llx x LL0 X Ca e1 : ℝ),

    0 ≤ DY → 0 < degu → (∀ c, 0 < volc c) → (∀ c c', volc c = volc c') →
    (∀ c, sl c = Pc c / ((DY + 1) * (volc c * degu))) →
    P = (∑ c, Pc c) → vol = (∑ c, volc c) →

    P = vol * hFl + (DY + 1) * (vol * degu) *
        (∑ τ, (A0 τ * (∑ i ∈ top N j, u' τ i) + b0 τ * (∑ i : Fin N, u' τ i))) + rest →

    0 ≤ hFl →
    (∀ τ, |(j : ℝ) * A0 τ + (N : ℝ) * b0 τ| ≤ K1 * N * (Real.log (B0 * rd) + Lchi)) →
    (∀ τ, -(K2 * (Real.log (B0 * rd) + Lchi)) ≤ A0 τ) →
    |rest| ≤ K5 * ((DY + 1) * (vol * degu) * spread) →
    0 ≤ K1 → 0 ≤ K2 → 0 ≤ K5 →

    0 ≤ Cs → spread ≤ Cs * (∑ τ, ∑ i, |u' τ i|) → 1 ≤ B0 → Real.log B0 ≤ CB * Real.log b →
    1 ≤ CB → 0 ≤ T → (T + DY + 1) * U1 ≤ U + PP → (∑ τ, ∑ i, |u' τ i|) ≤ U1 →

    Real.exp 1 ≤ b → 1 ≤ rd → 0 ≤ Lchi → 1 ≤ llx → 1 ≤ x →
    LL0 = Real.log (b * rd) * llx + Lchi + Real.log x →
    Ca = (K1 + K2) * CB + K5 * Cs → X = Ca * LL0 * (∑ τ, ∑ i, |u' τ i|) → e1 = Ca * LL0 * PP →
    0 ≤ X ∧ -X ≤ (∑ c, sl c) / (Fintype.card ι : ℝ) ∧ T * X ≤ Ca * LL0 * U + e1

end Formalism.ShimuraLimitIdentity
