import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformiserNormGapPadicEmbedding
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
open NumberField IsDedekindDomain Formalism.L2.Pj GlobalTheory.GeoTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformiser_norm_gap_padic_embedding : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]), ∃ ϖ : F, 0 < ‖φ ϖ‖ ∧ ‖φ ϖ‖ < 1 ∧ ∀ c : F, ‖φ c‖ < 1 → ‖φ c‖ ≤ ‖φ ϖ‖ := by
  first | exact @GlobalTheory.UnifGap.exists_unif_norm_gap | exact GlobalTheory.UnifGap.exists_unif_norm_gap | (intros; apply GlobalTheory.UnifGap.exists_unif_norm_gap <;> assumption)
