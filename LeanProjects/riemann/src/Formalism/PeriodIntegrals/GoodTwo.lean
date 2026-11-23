import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct

noncomputable section
open scoped ComplexConjugate

namespace PI.GoodTwo

open Formalism.L2.Th1.CM (HasCMBy omegaK jInv)
open Formalism.L2.Th1.F (scalePair)

def IntCurve {K : Type} [NormedField K] (W : WeierstrassCurve K) : Prop :=
  ‖W.a₁‖ ≤ 1 ∧ ‖W.a₂‖ ≤ 1 ∧ ‖W.a₃‖ ≤ 1 ∧ ‖W.a₄‖ ≤ 1 ∧ ‖W.a₆‖ ≤ 1 ∧ ‖W.Δ‖ = 1

def Half : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 8 = 7 → HasCMBy d L → ∀ ι : ℂ ≃+* ℂ_[2],
    ∃ (c : ℂ) (hc : c ≠ 0) (W : WeierstrassCurve ℂ_[2]),
      (W.c₄ / 12 = ι (scalePair L c hc).g₂ ∧ W.c₆ / 216 = ι (scalePair L c hc).g₃) ∧ IntCurve W

def Full : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 8 = 7 → HasCMBy d L → ∀ ι : ℂ ≃+* ℂ_[2],
    ∃ (c : ℂ) (hc : c ≠ 0) (W : WeierstrassCurve ℂ_[2]),
      (W.c₄ / 12 = ι (scalePair L c hc).g₂ ∧ W.c₆ / 216 = ι (scalePair L c hc).g₃) ∧ IntCurve W ∧ ‖W.a₁‖ = 1

def Twist : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (W : WeierstrassCurve K) (g2 g3 : K),
    W.Δ ≠ 0 → g2 ^ 3 - 27 * g3 ^ 2 ≠ 0 → W.c₄ ^ 3 * (g2 ^ 3 - 27 * g3 ^ 2) = 1728 * g2 ^ 3 * W.Δ →
    ∃ u : K, u ≠ 0 ∧ W.c₄ / 12 = u ^ 4 * g2 ∧ W.c₆ / 216 = u ^ 6 * g3

def JUnit : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 8 = 7 → HasCMBy d L → ∀ ι : ℂ ≃+* ℂ_[2], ‖ι (jInv L)‖ = 1

def disc (L : PeriodPair) : ℂ := L.g₂ ^ 3 - 27 * L.g₃ ^ 2

def IsIdxTwo (L L' : PeriodPair) : Prop :=
  ∃ t : ℂ, t ∉ L.lattice ∧ 2 * t ∈ L.lattice ∧ ∀ z, z ∈ L'.lattice ↔ (z ∈ L.lattice ∨ z - t ∈ L.lattice)

def TwoIsog : Prop :=
  ∀ L L' : PeriodPair, IsIdxTwo L L' → (disc L' + 16 * disc L) ^ 3 = jInv L * disc L' * disc L ^ 2

def NormPow : Prop :=
  ∀ d : ℕ, Squarefree d → d % 8 = 7 →
    ∃ (h : ℕ) (x y : ℤ), 0 < h ∧ Odd y ∧ x ^ 2 + x * y + (((d + 1) / 4 : ℕ) : ℤ) * y ^ 2 = 2 ^ h

def Chain : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), d % 8 = 7 → HasCMBy d L → ∀ (h : ℕ) (x y : ℤ), Odd y →
    x ^ 2 + x * y + (((d + 1) / 4 : ℕ) : ℤ) * y ^ 2 = 2 ^ h → ∀ π : ℂ, (π = x + y * omegaK d ∨ π = x + y * conj (omegaK d)) →
    ∃ M : ℕ → PeriodPair, M 0 = L ∧ (∀ i, HasCMBy d (M i)) ∧ (∀ i, i < h → IsIdxTwo (M i) (M (i + 1))) ∧
      ∀ z, z ∈ (M h).lattice ↔ π * z ∈ L.lattice

end PI.GoodTwo
