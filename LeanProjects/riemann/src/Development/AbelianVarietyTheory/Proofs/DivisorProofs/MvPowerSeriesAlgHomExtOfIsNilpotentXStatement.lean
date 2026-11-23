import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesAlgHomExtOfIsNilpotentX
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X : ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A], ∀ φ ψ : MvPowerSeries σ k →ₐ[k] A, (∀ i, IsNilpotent (φ (X i))) → (∀ i, φ (X i) = ψ (X i)) → φ = ψ := by
  first | exact @GlobalTheory.mvPowerSeries_algHom_ext_of_isNilpotent | exact GlobalTheory.mvPowerSeries_algHom_ext_of_isNilpotent | (intros; apply GlobalTheory.mvPowerSeries_algHom_ext_of_isNilpotent <;> assumption)
