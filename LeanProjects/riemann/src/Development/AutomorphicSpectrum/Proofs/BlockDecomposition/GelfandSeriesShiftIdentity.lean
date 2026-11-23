import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MultisetEq

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem gser_mul_prod : ∀ (n : ℕ) (c : Fin n → ℂ),
    (1 - PowerSeries.X * gser c) * ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2) * PowerSeries.X) =
      ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2 + 1) * PowerSeries.X) := by
  intro n c
  have h := GlobalTheory.Dec.GelfSepProof.gen (fun a => c a + ((n : ℂ) - 1) / 2)
  have e : gser c = PowerSeries.mk (fun k => ∑ a, ∑ b,
      (Formalism.REAL.Amat (fun a => c a + ((n : ℂ) - 1) / 2) ^ k) a b) := rfl
  rw [e]
  simpa only [map_add, map_one] using h

end GlobalTheory.CompanionTheory.WaveMult
