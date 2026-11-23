import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelCompactTranslateBound
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_compact_translate_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (Ω : Set (GAd σ J)), IsCompact Ω → Ω ⊆ minParOne σ J X → ∀ (K : Subgroup (GAd σ J)), IsCompact (K : Set (GAd σ J)) → ∀ c : ℝ, 0 < c → ∀ (C : Set (GAd σ J)), IsCompact C → ∃ t1 : ℝ, ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ K, ∀ γ : GRat σ J, (p * a * k)⁻¹ * ratEmb σ J γ * (p * a * k) ∈ C → ∀ j : Fin r, t1 < t j → (∀ j' : Fin r, j'.val = j.val + 1 → t1 * t j' < t j) → (∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, γ.1.1 *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0) := by
  first | exact @GlobalTheory.CompanionTheory.FlagKey.flag_key | exact GlobalTheory.CompanionTheory.FlagKey.flag_key | (intros; apply GlobalTheory.CompanionTheory.FlagKey.flag_key <;> assumption)
