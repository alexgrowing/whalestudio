import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalSchwartzLatticeCombination
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRightMemSB
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit GlobalTheory.GJReg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_schwartz_lattice_combination : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (φ : Matrix (Fin n) (Fin n) k → ℂ), φ ∈ SB (Matrix (Fin n) (Fin n) k) →
    (∀ g ∈ KO k (Fin n), ∀ X, φ (g.val * X) = φ X) →
    ∃ (m : ℕ) (c : Fin m → ℂ) (h : Fin m → GL (Fin n) k), φ = ∑ i, c i • latInd (h i) := by
  first | exact @GlobalTheory.GJReg.span_latInd_lat | exact GlobalTheory.GJReg.span_latInd_lat | (intros; apply GlobalTheory.GJReg.span_latInd_lat <;> assumption)
