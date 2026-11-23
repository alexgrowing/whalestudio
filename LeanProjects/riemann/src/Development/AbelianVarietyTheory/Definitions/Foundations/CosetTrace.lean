import Mathlib

noncomputable section

namespace GlobalTheory.AlmostEt

open scoped NNReal

variable {L : Type*} [Field L]

def ApproxRoot (p : ℕ) (v : Valuation L ℝ≥0) (F : Subfield L) : Prop :=
  ∃ θ : ℝ≥0, θ < 1 ∧ ∀ u ∈ F, ∃ w ∈ F, v (u - w ^ p) ≤ θ * v u

variable {G : Type*} [Group G] [MulSemiringAction G L]

abbrev Fix (L : Type*) [Field L] {G : Type*} [Group G] [MulSemiringAction G L] (N : Subgroup G) :
    Subfield L := FixedPoints.subfield N L

def Moves (v : Valuation L ℝ≥0) (F : Subfield L) (σ : G) : Prop :=
  ∀ r : ℝ≥0, r < 1 → ∃ x ∈ F, v x ≤ 1 ∧ r < v (σ • x - x)

structure IsSep (v : Valuation L ℝ≥0) (N : Subgroup G) {n : ℕ} (a b : Fin n → L) (c : L) : Prop where
  a_mem : ∀ i, a i ∈ Fix L N
  b_mem : ∀ i, b i ∈ Fix L N
  c_mem : c ∈ Fix L N
  a_le : ∀ i, v (a i) ≤ 1
  b_le : ∀ i, v (b i) ≤ 1
  c_le : v c ≤ 1
  sum_in : ∀ σ : G, σ ∈ N → ∑ i, a i * σ • b i = c
  sum_out : ∀ σ : G, σ ∉ N → ∑ i, a i * σ • b i = 0

def AlmostSep (v : Valuation L ℝ≥0) (N : Subgroup G) : Prop :=
  ∀ r : ℝ≥0, r < 1 → ∃ (n : ℕ) (a b : Fin n → L) (c : L), IsSep v N a b c ∧ r < v c

def cosetTrace (N : Subgroup G) [Fintype (G ⧸ N)] (x : L) : L := ∑ q : G ⧸ N, q.out • x

end GlobalTheory.AlmostEt
