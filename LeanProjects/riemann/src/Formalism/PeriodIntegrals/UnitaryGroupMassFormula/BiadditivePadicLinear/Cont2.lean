import Formalism.PeriodIntegrals.BiaddZpLin

noncomputable section

namespace PI.BiaddZpLinW

open PI.BiaddZpLin

def Cont2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.constantCoeff l = 0 →
    (∀ n : ℕ, Simeq (be l ex ph (mulBy l ex (n : ℂ_[p]) (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (MvPowerSeries.C (n : ℂ_[p]) * be l ex ph (Xv 0) (Xv 1))) →
    ∀ n : ℤ_[p], Simeq (be l ex ph (mulBy l ex (zc n) (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (MvPowerSeries.C (zc n) * be l ex ph (Xv 0) (Xv 1))

end PI.BiaddZpLinW
