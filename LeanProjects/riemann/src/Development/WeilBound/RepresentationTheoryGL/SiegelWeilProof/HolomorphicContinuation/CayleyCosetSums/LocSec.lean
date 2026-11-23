import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HolLeadHol

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def zOfE (x : M2 n) : Matrix (Fin n) (Fin n) ℂ := (Complex.I • x.toBlocks₁₁ + x.toBlocks₁₂) * (u1 x)⁻¹

def LocSec : Prop :=
  ∀ (n : ℕ) (Z₀ : Matrix (Fin n) (Fin n) ℂ), ((-(Complex.I / 2)) • (Z₀ - Z₀ᴴ)).PosDef →
    ∃ s : Matrix (Fin n) (Fin n) ℂ → M2 n, (∀ᶠ Z in 𝓝 Z₀, InG (s Z) ∧ (s Z).det ≠ 0 ∧ zOfE (s Z) = Z) ∧
      ContDiffAt ℝ 1 s Z₀

def Fib : Prop :=
  ∀ (n : ℕ) (y y' : GR n), zOfE (mR y) = zOfE (mR y') → InK (mR (y⁻¹ * y'))

end PositivityTheory.Rg.Sw.HSt
