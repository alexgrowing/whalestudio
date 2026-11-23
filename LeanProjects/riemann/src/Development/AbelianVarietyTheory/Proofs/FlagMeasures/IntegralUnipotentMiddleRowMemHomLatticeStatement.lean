import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentMiddleRowMemHomLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnipotent_middleRow_mem_homLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ a : Fin r, (fun w (l : Fin (k + 1)) => gM A γ w (eI k r a) (wI k r l)) ∈ homLat (σ : E →+* E) J Λ P f A (dInv E (r - a.val)) (s a) := by
  first | exact @GlobalTheory.SnMass.VolN.row_mem_homLat | exact GlobalTheory.SnMass.VolN.row_mem_homLat | (intros; apply GlobalTheory.SnMass.VolN.row_mem_homLat <;> assumption)
