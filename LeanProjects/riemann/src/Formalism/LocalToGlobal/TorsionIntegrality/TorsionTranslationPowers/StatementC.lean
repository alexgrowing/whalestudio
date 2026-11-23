import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementA
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CM4

noncomputable section

namespace Formalism.L2.Th1.E

def CMIntegrality : Prop :=
  ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]) (lam : ℂ_[l]), lam ≠ 0 →
    ‖lam ^ 4 * ι L.g₂‖ ≤ 1 → ‖lam ^ 6 * ι L.g₃‖ ≤ 1 →
    ‖(lam ^ 4 * ι L.g₂) ^ 3 - 27 * (lam ^ 6 * ι L.g₃) ^ 2‖ = 1 →
    ∀ (z : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * z ∈ L.lattice → z ∉ L.lattice →
      ‖lam ^ 2 * ι (L.weierstrassP z)‖ ≤ 1 ∧ ‖lam ^ 3 * ι (L.derivWeierstrassP z)‖ ≤ 1

def CMUnramifiedMembership : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 4 = 3 → Formalism.L2.Th1.CM.HasCMBy d L →
    ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ d → ∀ (ι : ℂ ≃+* ℂ_[l]) (lam : ℂ_[l]), lam ≠ 0 →
      (lam ^ 4 * ι L.g₂) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l → (lam ^ 6 * ι L.g₃) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l →
      ‖lam ^ 4 * ι L.g₂‖ ≤ 1 → ‖lam ^ 6 * ι L.g₃‖ ≤ 1 →
      ‖(lam ^ 4 * ι L.g₂) ^ 3 - 27 * (lam ^ 6 * ι L.g₃) ^ 2‖ = 1 →
    ∀ (z : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * z ∈ L.lattice → z ∉ L.lattice →
      lam ^ 2 * ι (L.weierstrassP z) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l ∧
        lam ^ 3 * ι (L.derivWeierstrassP z) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l

open Classical in

def ScaledTorsionPointNonsingular : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (lam : ℂ_[l]), lam ≠ 0 →
    ∀ (z : ℂ) (N : ℕ), (N : ℂ) * z ∈ L.lattice → z ∉ L.lattice →
      ∃ h : (Formalism.L2.Th1.A.shortW (lam ^ 4 * ι L.g₂) (lam ^ 6 * ι L.g₃)).toAffine.Nonsingular
          (lam ^ 2 * ι (L.weierstrassP z)) (lam ^ 3 * ι (L.derivWeierstrassP z) / 2),
        N • WeierstrassCurve.Affine.Point.some _ _ h = 0

def CMTorsionValuesOfIntegralAndUnramified : Prop := CMIntegrality → CMUnramifiedMembership → Formalism.L2.Th1.CM.CM4

end Formalism.L2.Th1.E
