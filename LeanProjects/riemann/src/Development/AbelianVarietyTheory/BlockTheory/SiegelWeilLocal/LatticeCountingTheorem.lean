import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem

open NumberField Formalism.MainNotions.S

def CountingTheorem : Prop :=
  ∀ Cg : ℝ, ∃ n₀ : ℕ, ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ),
    GlobalTheory.Count.CountHyp B Cg n₀ d p q b →
      FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) ∧
        |(B.D : ℝ) - GlobalTheory.Count.mainTerm B d| ≤
          Real.exp (-(1 / 16 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log (B.I.n : ℝ))) *
            GlobalTheory.Count.mainTerm B d

example (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ)
    (h : GlobalTheory.Count.CountHyp B Cg n₀ d p q b) : 0 ≤ Cg := by
  obtain ⟨-, -, -, -, -, -, hb, -, -, hg, hgb, -⟩ := h
  by_contra hC
  have hC' : Cg < 0 := not_le.mp hC
  have h1 : b ^ Cg < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) hC'
  have h2 : (1 : ℝ) ≤ (B.g : ℝ) := by exact_mod_cast hg
  linarith

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem
