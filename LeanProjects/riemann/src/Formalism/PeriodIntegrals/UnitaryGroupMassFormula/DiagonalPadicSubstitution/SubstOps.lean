import Formalism.PeriodIntegrals.BeDiagZp

noncomputable section

open Classical

namespace PI.BeDiagZp

def S0 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f g h f' g' : MvPowerSeries σ ℂ_[p]),
    Simeq f f ∧ (Simeq f g → Simeq g f) ∧ (Simeq f g → Simeq g h → Simeq f h) ∧
    (Simeq f g → Simeq f' g' → Simeq (f + f') (g + g'))

def S1 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ τ : Type) [Finite σ] (f g : MvPowerSeries σ ℂ_[p])
    (s : σ → MvPowerSeries τ ℂ_[p]),
    (∀ i, MvPowerSeries.constantCoeff (s i) = 0) → (∀ i, IntegralMv (s i)) →
    Simeq f g → Simeq (MvPowerSeries.subst s f) (MvPowerSeries.subst s g)

def SubstOps : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.constantCoeff l = 0 →
    ∀ (σ τ : Type) [Finite σ] (s : σ → MvPowerSeries τ ℂ_[p]),
    (∀ i, MvPowerSeries.constantCoeff (s i) = 0) →
    (∀ i, MvPowerSeries.subst s (Xv i : MvPowerSeries σ ℂ_[p]) = s i) ∧
    (∀ (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]),
      MvPowerSeries.subst s (MvPowerSeries.C c * a) = MvPowerSeries.C c * MvPowerSeries.subst s a) ∧
    (∀ a b : MvPowerSeries σ ℂ_[p],
      MvPowerSeries.subst s (a + b) = MvPowerSeries.subst s a + MvPowerSeries.subst s b) ∧
    ∀ a b : MvPowerSeries σ ℂ_[p], MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 →
      MvPowerSeries.constantCoeff (MvPowerSeries.subst s a) = 0 ∧
      MvPowerSeries.subst s (add l ex a b) = add l ex (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) ∧
      (∀ c, MvPowerSeries.subst s (mulBy l ex c a) = mulBy l ex c (MvPowerSeries.subst s a)) ∧
      MvPowerSeries.subst s (phAt ph a) = phAt ph (MvPowerSeries.subst s a) ∧
      MvPowerSeries.subst s (be l ex ph a b) = be l ex ph (MvPowerSeries.subst s a) (MvPowerSeries.subst s b)

def Ident : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex : PowerSeries ℂ_[p]),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    PowerSeries.constantCoeff l = 0 ∧
    ∀ (σ : Type) (a b : MvPowerSeries σ ℂ_[p]),
      MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 →
      MvPowerSeries.constantCoeff (add l ex a b) = 0 ∧
      (∀ c, MvPowerSeries.constantCoeff (mulBy l ex c a) = 0) ∧
      add l ex a b = add l ex b a ∧
      add l ex a a = mulBy l ex 2 a ∧
      (∀ c d, add l ex (mulBy l ex c a) (mulBy l ex d a) = mulBy l ex (c + d) a) ∧
      (∀ c, add l ex (mulBy l ex c a) a = mulBy l ex (c + 1) a) ∧
      mulBy l ex 1 a = a ∧
      mulBy l ex 0 a = 0

def Cont : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.constantCoeff l = 0 →
    (∀ n : ℕ, Simeq (be l ex ph (Xv ()) (mulBy l ex (n : ℂ_[p]) (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (n : ℂ_[p]) * be l ex ph (Xv ()) (Xv ()))) →
    ∀ n : ℤ_[p], Simeq (be l ex ph (Xv ()) (mulBy l ex (zc n) (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (zc n) * be l ex ph (Xv ()) (Xv ()))

end PI.BeDiagZp
