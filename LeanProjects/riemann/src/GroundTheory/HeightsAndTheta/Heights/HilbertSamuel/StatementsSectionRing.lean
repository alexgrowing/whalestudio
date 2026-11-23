import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionRingFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    ∃ (r : ℕ) (d : Fin r → ℕ) (e : Fin r → Ω), (∀ i, e i ∈ chartLat y a (d i)) ∧
      ∀ n : ℕ, chartLat y a n ≤ AddSubgroup.closure
        {s | ∃ (i : Fin r) (μ : Fin q → ℕ), d i + ∑ j, μ j = n ∧ s = e i * ∏ j, w j ^ μ j}

def SectionBounded.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : HermLine ι) (q : ℕ) (w : Fin q → Ω),
    (∀ j, w j ∈ chartLat y A.a 1) → KH.GeneratesOn y A.a w → (∀ j, IsSmallH (mCoordIdeal y) y A 1 (w j)) →
    ∀ (n : ℕ) (s : Ω), s ∈ chartLat y A.a n → ∃ C : ℝ, IsBoundedH (mCoordIdeal y) y A n C s

def SectionBoundedMul.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : HermLine ι) (n m : ℕ) (C C' : ℝ) (s t : Ω),
    s ∈ chartLat y A.a n → t ∈ chartLat y A.a m →
    IsBoundedH (mCoordIdeal y) y A n C s → IsBoundedH (mCoordIdeal y) y A m C' t →
    IsBoundedH (mCoordIdeal y) y A (n + m) (C * C') (s * t)

section Inhabitants

open ProjLine

theorem isBoundedH_one_of_isSmallH {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] {P : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {A : HermLine ι} {τ : ℕ} {s : Ω}
    (h : IsSmallH P y A τ s) : IsBoundedH P y A τ 1 s := by
  intro dg dh g h' z hg hh hdeg he hz
  rw [one_mul]
  exact h dg dh g h' z hg hh hdeg he hz

theorem SectionRingFinite.hyps_inhabited :
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) ∧ (∀ j : Fin 2, y ⟨(), j⟩ ∈ chartLat (ι := GlobalTheory (Fin 2)) y fsLine1.a 1) ∧
      KH.GeneratesOn (ι := GlobalTheory (Fin 2)) y fsLine1.a (fun j : Fin 2 => y ⟨(), j⟩) :=
  ⟨IntegralClosureFinite.hyps_inhabited.2.1, coord_mem_chartLat, generatesOn_coords⟩

theorem SectionBounded.hyps_inhabited :
    (∀ j : Fin 2, y ⟨(), j⟩ ∈ chartLat (ι := GlobalTheory (Fin 2)) y fsLine1.a 1) ∧
      KH.GeneratesOn (ι := GlobalTheory (Fin 2)) y fsLine1.a (fun j : Fin 2 => y ⟨(), j⟩) ∧
      ∀ j : Fin 2, IsSmallH (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) y fsLine1 1 (y ⟨(), j⟩) :=
  ⟨coord_mem_chartLat, generatesOn_coords, isSmallH_coord⟩

theorem SectionBoundedMul.hyps_inhabited :
    y ⟨(), 0⟩ ∈ chartLat (ι := GlobalTheory (Fin 2)) y fsLine1.a 1 ∧ y ⟨(), 1⟩ ∈ chartLat (ι := GlobalTheory (Fin 2)) y fsLine1.a 1 ∧
      IsBoundedH (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) y fsLine1 1 1 (y ⟨(), 0⟩) ∧
      IsBoundedH (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) y fsLine1 1 1 (y ⟨(), 1⟩) :=
  ⟨coord_mem_chartLat 0, coord_mem_chartLat 1, isBoundedH_one_of_isSmallH (isSmallH_coord 0),
    isBoundedH_one_of_isSmallH (isSmallH_coord 1)⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
