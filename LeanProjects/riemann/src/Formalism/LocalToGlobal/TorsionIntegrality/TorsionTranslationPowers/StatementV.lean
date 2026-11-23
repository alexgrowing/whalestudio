import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementA
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementE

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

def VIntegral : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]), l ≠ 2 → IntCurve (curveL l L ι) →
    ∀ ε : ℂ_[l], ‖ε‖ = 1 → (∀ n, ‖coeff n (Formalism.L2.Th1.D.thetaS l (ι L.g₂) (ι L.g₃) ε)‖ ≤ 1) →
    ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    ∀ (s : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * s ∈ L.lattice →
      IntS (Formalism.L2.Th1.B.fExp (Formalism.L2.Th1.D.phFF l (ι L.g₂) (ι L.g₃) (ι (Formalism.L2.Th1.F.s2 L)) ε) *
        (PowerSeries.map (ι : ℂ →+* ℂ_[l])
          (Formalism.L2.Th1.F.taylor0 (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))).subst
          (C ε * Formalism.InvariantFactorPaths.G7.lgF ℂ_[l] l))

end Formalism.L2.Th1.E
