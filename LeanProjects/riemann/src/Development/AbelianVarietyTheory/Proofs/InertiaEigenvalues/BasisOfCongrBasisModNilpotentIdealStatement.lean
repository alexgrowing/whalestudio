import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BasisOfCongrBasisModNilpotentIdeal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basis_of_congr_basis_mod_nilpotent_ideal : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (ι : Type) (b b' : ι → M) (I : Ideal R) (n : ℕ), I ^ n = ⊥ → LinearIndependent R b → Submodule.span R (Set.range b) = ⊤ → (∀ k, b' k - b k ∈ I • (⊤ : Submodule R M)) → LinearIndependent R b' ∧ Submodule.span R (Set.range b') = ⊤ := by
  first | exact @GlobalTheory.BSP.family_congr_basis_mod_nilpotent | exact GlobalTheory.BSP.family_congr_basis_mod_nilpotent | (intros; apply GlobalTheory.BSP.family_congr_basis_mod_nilpotent <;> assumption)
