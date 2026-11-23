import Mathlib
import Formalism.PeriodIntegrals.PhNormUnits

noncomputable section

open Classical Filter Topology

namespace PI.PhNormUnits.UnitaryGroupMassFormula

open PI.PhNormUnits

def Hyp (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])) : Prop :=
  PowerSeries.constantCoeff ex = 0 ∧ PowerSeries.subst ex l = PowerSeries.X ∧ p ≠ 2 ∧
    ((2 : ℂ_[p]), (2 : ℂ_[p])) ∈ S ∧ (∀ α ∈ S, α.swap ∈ S) ∧ (∀ α ∈ S, ∀ β ∈ S, α + β ∈ S) ∧
    (∀ α ∈ S, ∀ β ∈ S, α * β ∈ S) ∧
    (∀ α ∈ S, IntegralMv (mulBy l ex α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) ∧
    IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) ∧
    (∀ α ∈ S, ∃ n : ℤ_[p], α.1 + α.2 = zc n) ∧ (∀ α ∈ S, ∃ n : ℤ_[p], α.1 * α.2 = zc n) ∧
    (∀ α ∈ S, ∃ β ∈ S, ∃ γ ∈ S, ‖β.1‖ = 1 ∧ ‖β.2‖ = 1 ∧ ‖γ.1‖ = 1 ∧ ‖γ.2‖ = 1 ∧ α = β + γ) ∧
    Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)) ∧
    (∀ α ∈ S, ‖α.1‖ = 1 → ‖α.2‖ = 1 → Simeq (phAt ph (mulBy l ex α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * phAt ph (Xv ())))

def NormRel (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (α : ℂ_[p] × ℂ_[p]) : Prop :=
  Simeq (phAt ph (mulBy l ex α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
    (MvPowerSeries.C (α.1 * α.2) * phAt ph (Xv ()))

def SwapRel (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (α : ℂ_[p] × ℂ_[p]) : Prop :=
  Simeq (be l ex ph (mulBy l ex α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
    (be l ex ph (Xv 0) (mulBy l ex α.2 (Xv 1)))

def TraceRel (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (δ : ℂ_[p] × ℂ_[p]) : Prop :=
  Simeq (be l ex ph (Xv ()) (mulBy l ex δ.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
    (MvPowerSeries.C (δ.1 + δ.2) * phAt ph (Xv ()))

def StepUnits : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyp p l ex ph S →
    ∀ α ∈ S, ‖α.1‖ = 1 → ‖α.2‖ = 1 → SwapRel p l ex ph α

def StepAll : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyp p l ex ph S →
    (∀ α ∈ S, ‖α.1‖ = 1 → ‖α.2‖ = 1 → SwapRel p l ex ph α) → ∀ α ∈ S, SwapRel p l ex ph α

def StepTrace : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyp p l ex ph S →
    (∀ α ∈ S, SwapRel p l ex ph α) → ∀ δ ∈ S, TraceRel p l ex ph δ

def StepSum : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyp p l ex ph S →
    (∀ α ∈ S, SwapRel p l ex ph α) → (∀ δ ∈ S, TraceRel p l ex ph δ) → ∀ α ∈ S, NormRel p l ex ph α

theorem target_of_hyp (h : ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])),
    Hyp p l ex ph S → ∀ α ∈ S, NormRel p l ex ph α) : Target := by
  intro p _ l ex ph S h0 hX h2 hS2 hswap hadd hmul hint_r hadd2 htr hnm hdec hdef hunit α hα
  exact h p l ex ph S
    ⟨h0, hX, h2, hS2, hswap, hadd, hmul, hint_r, hadd2, htr, hnm, hdec, hdef, hunit⟩ α hα

theorem target_of_steps (hU : StepUnits) (hA : StepAll) (hT : StepTrace) (hS : StepSum) : Target := by
  refine target_of_hyp ?_
  intro p _ l ex ph S hH
  have hsw : ∀ α ∈ S, SwapRel p l ex ph α := hA p l ex ph S hH (hU p l ex ph S hH)
  exact hS p l ex ph S hH hsw (hT p l ex ph S hH hsw)

def CalcEquiv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f g h k : MvPowerSeries σ ℂ_[p]),
    Simeq f f ∧ (Simeq f g → Simeq g f) ∧ (Simeq f g → Simeq g h → Simeq f h) ∧
    (Simeq f g → Simeq h k → Simeq (f + h) (g + k)) ∧ (Simeq f g → Simeq (-f) (-g)) ∧
    (Simeq f g ↔ Simeq (f - g) 0)

def CalcSubst : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ τ : Type) [Finite σ] (a : σ → MvPowerSeries τ ℂ_[p]),
    (∀ i, MvPowerSeries.constantCoeff (a i) = 0) → (∀ i, IntegralMv (a i)) →
    (∀ f g : MvPowerSeries σ ℂ_[p], Simeq f g → Simeq (MvPowerSeries.subst a f) (MvPowerSeries.subst a g)) ∧
    (∀ f : MvPowerSeries σ ℂ_[p], IntegralMv f → IntegralMv (MvPowerSeries.subst a f))

def CalcClosed : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (F : ℕ → MvPowerSeries σ ℂ_[p]) (f : MvPowerSeries σ ℂ_[p]),
    (∀ e, Tendsto (fun k => MvPowerSeries.coeff e (F k)) atTop (𝓝 (MvPowerSeries.coeff e f))) →
    ((∀ k, Simeq (F k) 0) → Simeq f 0) ∧ ((∀ k, IntegralMv (F k)) → IntegralMv f)

def NatDense : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℤ_[p]), ∃ u : ℕ → ℕ, Tendsto (fun k => ((u k : ℕ) : ℂ_[p])) atTop (𝓝 (zc n))

def CalcZpScale : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f g : MvPowerSeries σ ℂ_[p]) (n : ℤ_[p]),
    Simeq f g → Simeq (MvPowerSeries.C (zc n) * f) (MvPowerSeries.C (zc n) * g)

end PI.PhNormUnits.UnitaryGroupMassFormula
