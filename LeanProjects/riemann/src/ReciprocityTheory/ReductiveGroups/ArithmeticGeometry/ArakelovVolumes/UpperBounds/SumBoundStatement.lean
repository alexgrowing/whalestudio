import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexOrder

noncomputable section

def Jf (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  Matrix.fromBlocks 1 0 0 (-1)

def IsUpq {p q : ℕ} (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) : Prop := gᴴ * Jf p q * g = Jf p q

def mob {p q : ℕ} (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Z : Matrix (Fin p) (Fin q) ℂ) :
    Matrix (Fin p) (Fin q) ℂ :=
  (g.toBlocks₁₁ * Z + g.toBlocks₁₂) * (g.toBlocks₂₁ * Z + g.toBlocks₂₂)⁻¹

def dpow {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) (s : ℝ) : ℝ := (1 - Z * Zᴴ).det.re ^ s

def DetIntStatement : Prop :=
  ∀ (f p q : ℕ) (s : ℝ), ((p + q : ℕ) : ℝ) - 1 < s →
    ∫⁻ v in Dset f p q, ENNReal.ofReal (∏ k, dpow (Zof v k) (s - (p + q : ℕ))) < ⊤

def SumBoundStatement : Prop :=
  ∀ (f p q : ℕ) (s : ℝ), 2 * (f : ℝ) * ((p + q : ℕ) : ℝ) ^ 2 < s →
    ∀ (Γ : Subgroup (Fin f → GL (Fin p ⊕ Fin q) ℂ)), DiscreteTopology Γ →
    (∀ γ ∈ Γ, ∀ k, IsUpq ((γ k : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) →
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ v ∈ Dset f p q,
      ∑' γ : Γ, ENNReal.ofReal (∏ k, dpow (mob ((γ.1 k : GL (Fin p ⊕ Fin q) ℂ) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Zof v k)) s) ≤ C

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
