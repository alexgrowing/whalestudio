import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerNormInvariant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_centralizer_norm_invariant : ∀ {H : Type} [Group H] (θ : H →* H) (δ : H) (r : ℕ), 0 < r → (∀ h, (⇑θ)^[r] h = h) →
    (∀ z ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}, δ * θ z * δ⁻¹ ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}) ∧
    (∀ z ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}, (⇑((MulAut.conj δ).toMonoidHom.comp θ))^[r] z = z) := by
  first | (exact @GlobalTheory.LKMid.TwCent.main) | (exact GlobalTheory.LKMid.TwCent.main) | (intros; apply GlobalTheory.LKMid.TwCent.main  <;> assumption)
