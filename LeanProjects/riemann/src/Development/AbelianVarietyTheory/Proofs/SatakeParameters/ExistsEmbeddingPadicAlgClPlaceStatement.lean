import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsEmbeddingPadicAlgClPlace
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicAlgCl_embedding_and_place_norm_lt_one : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime], ∃ (τ : E →+* PadicAlgCl l) (w : HeightOneSpectrum (𝓞 E)), ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal := by
  first | exact @GlobalTheory.exists_embedding_padicAlgCl_place | exact GlobalTheory.exists_embedding_padicAlgCl_place | (intros; apply GlobalTheory.exists_embedding_padicAlgCl_place <;> assumption)
