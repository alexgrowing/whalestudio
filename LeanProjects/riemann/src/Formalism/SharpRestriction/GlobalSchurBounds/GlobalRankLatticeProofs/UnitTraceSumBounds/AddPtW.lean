import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions

namespace Formalism.MainNotions.Ext

def PtW {p : ℕ} [Fact p.Prime] {σ : Type} (a : MvPowerSeries σ ℂ_[p]) : Prop :=
  IntegralW a ∧ MvPowerSeries.constantCoeff a = 0

def AddPtW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → IntegralW (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    ∀ (σ : Type) (a b : MvPowerSeries σ ℂ_[p]), PtW a → PtW b → PtW (g.add a b)

def MulPtW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → ∀ c : ℂ_[p], IntegralW (g.mulBy c (Xv ()) : MvPowerSeries Unit ℂ_[p]) →
    ∀ (σ : Type) (a : MvPowerSeries σ ℂ_[p]), PtW a → PtW (g.mulBy c a)

def LinPtW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → IntegralW (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    ∀ (ι : Type) [Fintype ι] (c : ι → ℂ_[p]), (∀ j, IntegralW (g.mulBy (c j) (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    ∀ (σ : Type) (a : ι → MvPowerSeries σ ℂ_[p]), (∀ j, PtW (a j)) → PtW (g.lin c a)

end Formalism.MainNotions.Ext
