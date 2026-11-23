import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementA
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementS

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

section Gen

variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l])

def Unif : Prop := Formalism.L2.Th1.A.g₂ W = ι L.g₂ ∧ Formalism.L2.Th1.A.g₃ W = ι L.g₃

open Classical in

def ptW (t : ℂ) : W.toAffine.Point :=
  if h : t ∉ L.lattice ∧ W.toAffine.Nonsingular (ι (L.weierstrassP t) - W.b₂ / 12)
      ((ι (L.derivWeierstrassP t) - W.a₁ * (ι (L.weierstrassP t) - W.b₂ / 12) - W.a₃) / 2)
  then .some _ _ h.2 else 0

def inW (f : ℂ → ℂ) : PowerSeries ℂ_[l] :=
  (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.taylor0 f)).subst (Formalism.L2.Th1.A.logSer W)

def phW : PowerSeries ℂ_[l] :=
  Formalism.L2.Th1.B.phO (ι (Formalism.L2.Th1.F.s2 L)) (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.pSeries L))
    (Formalism.L2.Th1.A.logSer W)

def gW (t : ℂ) : PowerSeries ℂ_[l] :=
  Formalism.L2.Th1.B.fExp (phW l L ι W) * inW l ι W (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L))

end Gen

open Classical in

def PtWAdd : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    ∀ s t : ℂ, ptW l L ι W (s + t) = ptW l L ι W s + ptW l L ι W t

def PtWZero : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    ∀ t : ℂ, ptW l L ι W t = 0 ↔ t ∈ L.lattice

open Classical in

def AnalyticSysW : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    ∀ (π : ℂ →+ W.toAffine.Point), (∀ t, π t = ptW l L ι W t) → IsTransSys W π (gW l L ι W)

def AnalyticTransW : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    IntCurve W →
    ∀ (t : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * t ∈ L.lattice → t ∉ L.lattice →
      ‖ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0)‖ = 1 ∧
      OneUnit (C (ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0))⁻¹ * gW l L ι W t)

def ShiftAnalyticW : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    IntCurve W → ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    ‖px W (ptW l L ι W (ω₀ / 2))‖ ≤ 1 → OneUnit (inW l ι W (Formalism.L2.Th1.F.th0 L (ω₀ / 2))) →
    ∀ (s : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * s ∈ L.lattice →
      GaussOne (inW l ι W (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))

end Formalism.L2.Th1.E
