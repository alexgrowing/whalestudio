import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PeriodLatticeAgreement

open Formalism.MainNotions.TaylorLogMetric
open scoped UpperHalfPlane

def latt (ω₁ τ : ℂ) : AddSubgroup ℂ where
  carrier := {w | ∃ m n : ℤ, w = ω₁ * ((m : ℂ) + (n : ℂ) * τ)}
  zero_mem' := ⟨0, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨m, n, rfl⟩ ⟨m', n', rfl⟩
    exact ⟨m + m', n + n', by push_cast; ring⟩
  neg_mem' := by
    rintro _ ⟨m, n, rfl⟩
    exact ⟨-m, -n, by push_cast; ring⟩

def scale (c : ℂ) (Λ : AddSubgroup ℂ) : AddSubgroup ℂ := Λ.map (AddMonoidHom.mulLeft c)

def period (Λ : AddSubgroup ℂ) : ℝ := ‖discr Λ‖ ^ ((1 : ℝ) / 6) * area Λ / Real.pi

def DiscrEta : Prop :=
  ∀ (ω₁ : ℂ) (τ : ℍ), ω₁ ≠ 0 →
    discr (latt ω₁ τ) = (2 * (Real.pi : ℂ) / ω₁) ^ 12 * ModularForm.eta (τ : ℂ) ^ 24

def AreaEq : Prop :=
  ∀ (ω₁ : ℂ) (τ : ℍ), ω₁ ≠ 0 → area (latt ω₁ τ) = ‖ω₁‖ ^ 2 * τ.im

def PeriodEta : Prop :=
  ∀ (ω₁ : ℂ) (τ : ℍ), ω₁ ≠ 0 →
    period (latt ω₁ τ) = 4 * Real.pi * τ.im * ‖ModularForm.eta (τ : ℂ)‖ ^ 4

def DiscrScale : Prop :=
  ∀ (ω₁ : ℂ) (τ : ℍ) (c : ℂ), ω₁ ≠ 0 → c ≠ 0 →
    discr (scale c (latt ω₁ τ)) = c ^ (-12 : ℤ) * discr (latt ω₁ τ)

def AgreePeriodPair : Prop :=
  ∀ L : PeriodPair,
    (∀ k : ℕ, 2 ≤ k →
      Summable (fun w : {w : ℂ // w ∈ L.lattice.toAddSubgroup ∧ w ≠ 0} => 1 / (w : ℂ) ^ (2 * k)) ∧
      eisG L.lattice.toAddSubgroup k = L.G (2 * k)) ∧
    g2 L.lattice.toAddSubgroup = L.g₂ ∧ g3 L.lattice.toAddSubgroup = L.g₃

def LatticePeriodEta : Prop :=
  DiscrEta ∧ AreaEq ∧ PeriodEta ∧ DiscrScale ∧ AgreePeriodPair

theorem mem_latt {ω₁ τ w : ℂ} : w ∈ latt ω₁ τ ↔ ∃ m n : ℤ, w = ω₁ * ((m : ℂ) + (n : ℂ) * τ) := Iff.rfl

theorem mem_scale {c w : ℂ} {Λ : AddSubgroup ℂ} : w ∈ scale c Λ ↔ ∃ v ∈ Λ, c * v = w := by
  simp [scale, AddSubgroup.mem_map]

theorem scale_latt (c ω₁ τ : ℂ) : scale c (latt ω₁ τ) = latt (c * ω₁) τ := by
  ext w
  rw [mem_scale, mem_latt]
  constructor
  · rintro ⟨_, ⟨m, n, rfl⟩, rfl⟩
    exact ⟨m, n, by ring⟩
  · rintro ⟨m, n, rfl⟩
    exact ⟨_, ⟨m, n, rfl⟩, by ring⟩

example : Complex.I ∈ latt 1 Complex.I ∧ (1 / 2 : ℂ) ∉ latt 1 Complex.I := by
  refine ⟨⟨0, 1, by simp⟩, ?_⟩
  rintro ⟨m, n, h⟩
  have h1 := congrArg Complex.re h
  simp at h1
  have h2 : ((2 * m : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by push_cast; linarith
  have := Int.cast_injective h2
  omega

end GlobalTheory.IndefiniteRowSideFullHecke.PeriodLatticeAgreement
