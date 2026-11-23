import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

open MeasureTheory NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DeepSet

open Formalism.MainNotions.S GlobalTheory.Count

def deepSet (B : RowsAut) (q : ℕ) (b : ℝ) : Set B.I.GA :=
  {x | x ∈ B.fund ∧ least B.I x < tauStar B q b}

def DeepBound : Prop :=
  ∀ Cg : ℝ, 0 ≤ Cg → ∃ n₀ : ℕ, ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ),
    1 ≤ q → CountHyp B Cg n₀ d p q b →
      ∫⁻ x in deepSet B q b, ENNReal.ofReal (kern B.I (phe B d) x x).re ∂(B.I.muA B.μf) ≤
        ENNReal.ofReal ((B.D : ℝ) * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))))

example (B : RowsAut) (q : ℕ) (b : ℝ) : deepSet B q b ⊆ B.fund := fun _ h => h.1

example (B : RowsAut) (q : ℕ) (b : ℝ) : tauStar B q b = (bigX B b ^ (11 * q))⁻¹ := by
  simp [tauStar]

end GlobalTheory.IndefiniteRowSideFullHecke.DeepSet
