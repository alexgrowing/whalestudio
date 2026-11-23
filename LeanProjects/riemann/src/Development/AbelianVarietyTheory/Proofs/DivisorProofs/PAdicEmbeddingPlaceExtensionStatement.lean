import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicEmbeddingPlaceExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
open NumberField IsDedekindDomain GlobalTheory.TrueGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_embedding_place_extension : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (ι : AlgebraicClosure F →+* ℂ_[p]), ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v), (p : 𝓞 F) ∈ v.asIdeal ∧ ∀ a, ‖ι a‖ ≤ 1 ↔ a ∈ e.O := by
  first | exact @GlobalTheory.TrueGeo.ExtOfEmb.exists_ext | exact GlobalTheory.TrueGeo.ExtOfEmb.exists_ext | (intros; apply GlobalTheory.TrueGeo.ExtOfEmb.exists_ext <;> assumption)
