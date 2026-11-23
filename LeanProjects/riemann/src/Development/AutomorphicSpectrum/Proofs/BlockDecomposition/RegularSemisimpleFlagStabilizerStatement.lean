import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularSemisimpleFlagStabilizer
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_semisimple_flag_stabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (γ : GRat σ J), GlobalTheory.Orb.IsRegSS γ.1.1 → (∀ j ∈ S, (∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, γ.1.1 *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0)) → ∃ g : GRat σ J, (∀ j ∈ S, (∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, g.1.1 *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0)) ∧ ∀ j ∈ S, (∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, (g⁻¹ * γ * g).1.1 *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0) ∧ (∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, (g⁻¹ * γ * g).1.1 *ᵥ (fun a => Y a l) = Y *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0) := by
  first | exact @GlobalTheory.CompanionTheory.LeviConj.conj_into_levi | exact GlobalTheory.CompanionTheory.LeviConj.conj_into_levi | (intros; apply GlobalTheory.CompanionTheory.LeviConj.conj_into_levi <;> assumption)
