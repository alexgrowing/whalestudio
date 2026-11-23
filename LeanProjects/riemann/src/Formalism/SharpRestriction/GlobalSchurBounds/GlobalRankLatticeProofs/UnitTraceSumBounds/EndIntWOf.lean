import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions

namespace Formalism.MainNotions.Ext

def CoefWfRing : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f g : MvPowerSeries σ ℂ_[p]), CoefWf f → CoefWf g →
    CoefWf (f + g) ∧ CoefWf (f - g) ∧ CoefWf (f * g) ∧ ∀ c : ℂ_[p], InWf c → CoefWf (MvPowerSeries.C c * f)

def SubstWf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]),
    CoefWf f → IntegralW a → MvPowerSeries.constantCoeff a = 0 → CoefWf (PowerSeries.subst a f)

def LogWf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → ModelOverW g.lam g.abelian₂ g.C → CoefWf g.l ∧ CoefWf g.ex

def EndIntWG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → ModelOverW g.lam g.abelian₂ g.C → ∀ α ∈ W2pair p,
    IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p]) →
    IntegralW (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])

theorem endIntW_of (H : EndIntWG) (D : D7) (hO : okpInert D) : StatementEndomorphismIntegralWitt D := by
  intro hE p _ cc δ g hA h5 hI hM α hα
  have hp2 : p ≠ 2 := by omega
  have hW : α ∈ W2pair p := by
    rw [← hO p g.lam hp2 hI]
    exact hα
  exact H p g hA.2.2.2.2 hM α hW (hE p cc δ g hA α hα)

def PhEvenG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → (∀ z, sgStar g.abelian₂ (-z) = -sgStar g.abelian₂ z) →
    g.W.a₁ = 0 → g.W.a₃ = 0 →
    (g.mulBy (-1) (Xv ()) : MvPowerSeries Unit ℂ_[p]) = -Xv () ∧
    (g.phAt (-Xv ()) : MvPowerSeries Unit ℂ_[p]) = g.phAt (Xv ())

end Formalism.MainNotions.Ext
