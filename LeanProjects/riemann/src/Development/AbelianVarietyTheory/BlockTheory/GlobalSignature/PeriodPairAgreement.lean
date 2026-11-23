import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PeriodPairAgreement

open Formalism.MainNotions.TaylorLogMetric

def lat (ω₁ τ : ℂ) : AddSubgroup ℂ := AddSubgroup.closure {ω₁, ω₁ * τ}

def scale (c : ℂ) (Λ : AddSubgroup ℂ) : AddSubgroup ℂ := Λ.map (AddMonoidHom.mulLeft c)

def period (Λ : AddSubgroup ℂ) : ℝ := ‖discr Λ‖ ^ ((1 : ℝ) / 6) * area Λ / Real.pi

def DiscrEta : Prop :=
  ∀ ω₁ τ : ℂ, ω₁ ≠ 0 → 0 < τ.im →
    discr (lat ω₁ τ) = (2 * (Real.pi : ℂ) / ω₁) ^ 12 * ModularForm.eta τ ^ 24

def AreaFormula : Prop :=
  ∀ ω₁ τ : ℂ, ω₁ ≠ 0 → 0 < τ.im → area (lat ω₁ τ) = ‖ω₁‖ ^ 2 * τ.im

def PeriodEta : Prop :=
  ∀ ω₁ τ : ℂ, ω₁ ≠ 0 → 0 < τ.im →
    period (lat ω₁ τ) = 4 * Real.pi * τ.im * ‖ModularForm.eta τ‖ ^ 4

def DiscrScale : Prop :=
  ∀ ω₁ τ c : ℂ, ω₁ ≠ 0 → 0 < τ.im → c ≠ 0 →
    discr (scale c (lat ω₁ τ)) = c ^ (-12 : ℤ) * discr (lat ω₁ τ)

def AgreePeriodPair : Prop :=
  ∀ L : PeriodPair,
    (∀ k : ℕ, 2 ≤ k → eisG L.lattice.toAddSubgroup k = L.G (2 * k)) ∧
    g2 L.lattice.toAddSubgroup = L.g₂ ∧ g3 L.lattice.toAddSubgroup = L.g₃

def LatticePeriodEta : Prop :=
  DiscrEta ∧ AreaFormula ∧ PeriodEta ∧ DiscrScale ∧ AgreePeriodPair

def pair (ω₁ τ : ℂ) (h₁ : ω₁ ≠ 0) (h : 0 < τ.im) : PeriodPair where
  ω₁ := ω₁
  ω₂ := ω₁ * τ
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h2 : ω₁ * ((s : ℂ) + (t : ℂ) * τ) = 0 := by
      rw [← hst]; simp only [Complex.real_smul]; ring
    have h3 : (s : ℂ) + (t : ℂ) * τ = 0 := (mul_eq_zero.mp h2).resolve_left h₁
    have hi := congrArg Complex.im h3
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_mul,
      add_zero, zero_add, Complex.zero_im] at hi
    have ht : t = 0 := (mul_eq_zero.mp hi).resolve_right h.ne'
    subst ht
    simpa using h3

end GlobalTheory.IndefiniteRowSideFullHecke.PeriodPairAgreement
