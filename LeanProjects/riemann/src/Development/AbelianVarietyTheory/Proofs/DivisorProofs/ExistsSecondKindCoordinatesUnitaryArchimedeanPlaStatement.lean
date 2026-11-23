import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecondKindCoordinatesUnitaryArchimedeanPla
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut Filter Topology
open scoped TensorProduct ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_secondKindCoordinates_unitaryArchimedeanPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ w : InfinitePlace F, ∃ (d : ℕ) (η : Fin d → ℝ → GAd σ J) (s : GArch σ J w → Fin d → ℝ), (∀ i, IsRealLine σ J (η i)) ∧ Tendsto s (𝓝 1) (𝓝 0) ∧ ∀ᶠ y in 𝓝 1, embArch σ J w y = (List.ofFn fun i => η i (s y i)).prod := by
  first | exact @GlobalTheory.UAut.exists_coordSecondKind_arch | exact GlobalTheory.UAut.exists_coordSecondKind_arch | (intros; apply GlobalTheory.UAut.exists_coordSecondKind_arch <;> assumption)
