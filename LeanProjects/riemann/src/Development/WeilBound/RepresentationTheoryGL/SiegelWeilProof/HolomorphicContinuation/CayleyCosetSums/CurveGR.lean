import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.RcCongr

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def dir1 (Z : M2 n) : M2 n := (1 / 2 : ℂ) • (Z + sig Z)

def dir2 (Z : M2 n) : M2 n := (1 / (2 * Complex.I)) • (Z - sig Z)

def CurveGR : Prop :=
  ∀ (n : ℕ) (Z : M2 n) (b : Bool), ∃ γ : ℝ → GR n, Continuous γ ∧ γ 0 = 1 ∧
    (∀ s t, γ (s + t) = γ s * γ t) ∧
    ∀ t, mR (γ t) = NormedSpace.exp ((t : ℂ) • (if b then dir1 Z else dir2 Z))

def FzDer : Prop :=
  ∀ (n m : ℕ) (e : ℤ) (w : ℂ) (Z : M2 n) (b : Bool), ∃ C : ℝ, 0 ≤ C ∧ ∀ y : GR n,
    ∃ R : ℂ, HasDerivAt (fun s : ℝ => fz m e w (mR y * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) R 0 ∧
      ‖R‖ ≤ C * ‖fz m e w (mR y)‖

end PositivityTheory.Rg.Sw.HSt
