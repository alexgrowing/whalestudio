import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

namespace Formalism.MainNotions.Ext.CutA

def SimeqGroup : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f g : MvPowerSeries σ ℂ_[p]), Simeq f 0 → Simeq g 0 →
    Simeq (f + g) 0 ∧ Simeq (-f) 0

def SimeqZp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f : MvPowerSeries σ ℂ_[p]), Simeq f 0 →
    ∀ n : ℤ_[p], Simeq (MvPowerSeries.C (zc n) * f) 0

def SimeqSubst : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ τ : Type) [Fintype σ] [Fintype τ] (f : MvPowerSeries σ ℂ_[p])
    (s : σ → MvPowerSeries τ ℂ_[p]), (∀ i, MvPowerSeries.constantCoeff (s i) = 0) → (∀ i, IntegralMv (s i)) →
    Simeq f 0 → Simeq (MvPowerSeries.subst s f) 0

def SimeqLimit : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f : ℕ → MvPowerSeries σ ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]),
    (∀ α, Filter.Tendsto (fun k => MvPowerSeries.coeff α (f k)) Filter.atTop (nhds (MvPowerSeries.coeff α F))) →
    (∀ k, Simeq (f k) 0) → Simeq F 0

def SimeqPd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) [DecidableEq σ] (f : MvPowerSeries σ ℂ_[p]), Simeq f 0 →
    ∀ k : σ, IntegralMv (pd k f)

def BiaddZp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    Simeq (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) →
    ∀ n : ℤ_[p], Simeq (g.be (g.mulBy (zc n) (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (MvPowerSeries.C (zc n) * g.be (Xv 0) (Xv 1))

end Formalism.MainNotions.Ext.CutA
