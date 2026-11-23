import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.GoodLat
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelMoves

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Mv

open Formalism.L2.Th1.H

def HeisU : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B : AddSubgroup V), IsHerm H →
    IsSemiChar H A α → IsSemiChar H B α → IsBichar (cU H A B) ∧ IsHeis (cU H A B) (wA H α A) (wB H α B)

def InterSelf : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (Λ : AddSubgroup V), IsHerm H →
    IsSemiChar H Λ α → ∀ θ ∈ fixedBy H α Λ, inter H α Λ Λ θ = θ

def MovesU : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ₀ Λ₁ : AddSubgroup V), IsHerm H →
    IsSemiChar H A α → IsSemiChar H B α → GoodLat H α A B Λ₀ → GoodLat H α A B Λ₁ → relIdx Λ₀ Λ₁ ≠ 0 →
    ∀ θ ∈ fixedBy H α Λ₀, ∀ Xi : Sch (cU H A B) (Λ₀.addSubgroupOf A) →ₗ[ℂ] (V → ℂ),
      IsXi (cU H A B) (wA H α A) (wB H α B) (Λ₀.addSubgroupOf A) θ Xi →
      ∃ h : ind ((Λ₁.addSubgroupOf A : AddSubgroup A) : Set A) ∈ Sch (cU H A B) (Λ₀.addSubgroupOf A),
        0 < volA A Λ₀ Λ₁ ∧
        inter H α Λ₀ Λ₁ θ = (((Real.sqrt (volA A Λ₀ Λ₁))⁻¹ : ℝ) : ℂ) • Xi ⟨_, h⟩

def MovesComposeU : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ₀ Λ₁ Λ₂ : AddSubgroup V), IsHerm H →
    IsSemiChar H A α → IsSemiChar H B α → GoodLat H α A B Λ₀ → GoodLat H α A B Λ₁ → GoodLat H α A B Λ₂ →
    relIdx Λ₀ Λ₁ ≠ 0 → relIdx Λ₁ Λ₂ ≠ 0 → relIdx Λ₀ Λ₂ ≠ 0 →
    ∀ θ ∈ fixedBy H α Λ₀, inter H α Λ₁ Λ₂ (inter H α Λ₀ Λ₁ θ) = inter H α Λ₀ Λ₂ θ

def GenModelXi : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (Λ₀ : AddSubgroup V) (M ι : Type)
    (Λ : ι → AddSubgroup V) (Y : ι → Set M) (vol : ι → ℝ), IsHerm H →
    ∀ θ ∈ fixedBy H α Λ₀,
    (∀ s : Finset ι, ∃ (A B : AddSubgroup V) (φ : A → M), IsSemiChar H A α ∧ IsSemiChar H B α ∧
      GoodLat H α A B Λ₀ ∧ ∀ i ∈ s, GoodLat H α A B (Λ i) ∧ relIdx Λ₀ (Λ i) ≠ 0 ∧
        (∀ a : A, (a : V) ∈ Λ i ↔ φ a ∈ Y i) ∧ vol i = volA A Λ₀ (Λ i)) →
    ∃ Xi : (M → ℂ) →ₗ[ℂ] (V → ℂ), ∀ i, Xi (Set.indicator (Y i) 1) = ((Real.sqrt (vol i) : ℝ) : ℂ) • inter H α Λ₀ (Λ i) θ

end Formalism.L2.PairingIndexBounds.Mv
