import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitalIntegralsInvariantLocallyCon
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallisOrbitalIntegrals_invariant_locallyConstant : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (∀ (f' : Gl r F → ℂ) (g : GL (Fin r) F) (Y : Gl r F), orbG M f' (act g Y) = orbG M f' Y) ∧ (∀ (f : Hn r F E → ℂ) (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E), orbU M f (actU g X) = orbU M f X) ∧ (∀ (f' : Gl r F → ℂ), IsTest f' → ∀ a₀ : Inv r F, Delta a₀ ≠ 0 → ∀ᶠ a in 𝓝 a₀, orbG M f' (sec a) = orbG M f' (sec a₀)) ∧ ∀ (f : Hn r F E → ℂ), IsTest f → ∀ (a₀ : Inv r F) (X₀ : Hn r F E), Delta a₀ ≠ 0 → HasInv X₀ a₀ → ∀ᶠ a in 𝓝 a₀, (∃ X : Hn r F E, HasInv X a) ∧ ∀ X : Hn r F E, HasInv X a → orbU M f X = orbU M f X₀ := by
  first | exact @GlobalTheory.JR.OrbLC.orbital_integrals_invariant_locally_constant | exact GlobalTheory.JR.OrbLC.orbital_integrals_invariant_locally_constant | (intros; apply GlobalTheory.JR.OrbLC.orbital_integrals_invariant_locally_constant <;> assumption)
