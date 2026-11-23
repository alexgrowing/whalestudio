import ReciprocityTheory.ReducedBases.LatDefs

noncomputable section

namespace ReciprocityTheory.ReducedBases.T2

open ReciprocityTheory.ReducedBases Matrix

def C1 (d : ℕ) : ℝ := (d : ℝ) * (3 / 2 : ℝ) ^ d * (2 : ℝ) ^ ((d : ℝ) / 2 - 1)

def BilinBoundedBasis {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (e : Module.Basis (Fin d) ℤ (Fin d → ℤ)) : Prop :=
  ∀ (i : Fin d) (μ : Fin d → ℤ), |polar A (e i) μ| ≤ (d : ℝ) * (2 : ℝ) ^ ((d : ℝ) / 2) * polar A μ μ

def CoordBoundedOnMin {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (e : Module.Basis (Fin d) ℤ (Fin d → ℤ)) : Prop :=
  ∀ (N : ℤ), 1 ≤ N → ∀ α : Fin d → ℤ, IsMinInClass (Q A) N α →
    ∀ i : Fin d, |((e.repr α i : ℤ) : ℝ)| ≤ C1 d * (N : ℝ)

def ExistsBoundedBasis : Prop :=
  ∀ (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ), A.PosDef →
    ∃ e : Module.Basis (Fin d) ℤ (Fin d → ℤ), BilinBoundedBasis A e ∧ CoordBoundedOnMin A e

end ReciprocityTheory.ReducedBases.T2

end
