import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement

noncomputable section

namespace Formalism.L2.Th1.CM

def CM4 : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 4 = 3 → HasCMBy d L →
    ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ d → ∀ (ι : ℂ ≃+* ℂ_[l]) (lam : ℂ_[l]), lam ≠ 0 →
      (lam ^ 4 * ι L.g₂) ∈ MaximalUnramifiedExtension l → (lam ^ 6 * ι L.g₃) ∈ MaximalUnramifiedExtension l → ‖lam ^ 4 * ι L.g₂‖ ≤ 1 →
      ‖lam ^ 6 * ι L.g₃‖ ≤ 1 → ‖(lam ^ 4 * ι L.g₂) ^ 3 - 27 * (lam ^ 6 * ι L.g₃) ^ 2‖ = 1 →
    ∀ (z : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * z ∈ L.lattice → z ∉ L.lattice →
      lam ^ 2 * ι (L.weierstrassP z) ∈ MaximalUnramifiedExtension l ∧ lam ^ 3 * ι (L.derivWeierstrassP z) ∈ MaximalUnramifiedExtension l ∧
        ‖lam ^ 2 * ι (L.weierstrassP z)‖ ≤ 1 ∧ ‖lam ^ 3 * ι (L.derivWeierstrassP z)‖ ≤ 1

end Formalism.L2.Th1.CM
