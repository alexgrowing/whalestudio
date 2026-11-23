import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementV
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementW
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementW

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

def VJoint : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]), l ≠ 2 → IntCurve (curveL l L ι) →
    ∀ (g2 g3 s2 ε : Formalism.L2.Th1.CM.MaximalUnramifiedExtension l), (g2 : ℂ_[l]) = ι L.g₂ → (g3 : ℂ_[l]) = ι L.g₃ →
    (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 L) → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (Formalism.L2.Th1.D.thetaS l g2 g3 ε)‖ ≤ 1) →
    ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    ∀ (s : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * s ∈ L.lattice →
      ∃ V : PowerSeries ℂ_[l], IntS V ∧
        (Formalism.DworkPowerSeriesWeights.mvExp (-(PowerSeries.map (Formalism.L2.Th1.CM.MaximalUnramifiedExtension l).subtype
                  (Formalism.L2.Th1.D.phFF l g2 g3 s2 ε))) : PowerSeries ℂ_[l]) * V =
          (PowerSeries.map (ι : ℂ →+* ℂ_[l])
            (Formalism.L2.Th1.F.taylor0 (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))).subst
            (C (ε : ℂ_[l]) * Formalism.InvariantFactorPaths.G7.lgF ℂ_[l] l)

def PhWEq : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    phW l L ι W = Formalism.L2.Th1.B.phW W (ι (Formalism.L2.Th1.F.s2 L))

def InWTh0 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
      inW l ι W (Formalism.L2.Th1.F.th0 L (ω₀ / 2)) =
        Formalism.L2.Th1.B.fExp (-(Formalism.L2.Th1.B.evenSigmaLogAtTwoTorsion W (ι (Formalism.L2.Th1.F.s2 L)) (px W (ptW l L ι W (ω₀ / 2)))))

def ThetaZeroFromPhiDerivative : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    IntCurve W → ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    ‖px W (ptW l L ι W (ω₀ / 2))‖ ≤ 1 →
    Formalism.InvariantFactorPaths.G7.Simeq (ι := Unit)
      (Formalism.L2.Th1.B.evenSigmaLogAtTwoTorsion W (ι (Formalism.L2.Th1.F.s2 L)) (px W (ptW l L ι W (ω₀ / 2)))) 0 →
    ∀ (s : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * s ∈ L.lattice →
      GaussOne (inW l ι W (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))

end Formalism.L2.Th1.E
