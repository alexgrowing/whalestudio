import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeSupWiderBandGenCentralEigenforms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_le_sup_wider_band_genCentralEigenforms : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ (N : ℕ) (c : ℝ), 1 ≤ c → ∃ C : ℝ, ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ M : ℝ, (∀ h ∈ band E a, ‖φ.1 h‖ ≤ M) → ∀ g : GA E a, c⁻¹ ≤ absDetA g → absDetA g ≤ 2 * c → ‖φ.1 g‖ ≤ C * M := by
  first | exact @GlobalTheory.HCF.norm_le_of_band_wide | exact GlobalTheory.HCF.norm_le_of_band_wide | (intros; apply GlobalTheory.HCF.norm_le_of_band_wide <;> assumption)
