import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicEmbeddingOfDvr
import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
open NumberField IsDedekindDomain Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_embedding_of_dvr : ∀ {K : Type} [Field K] [NumberField K] (pl : HeightOneSpectrum (𝓞 K)) (p : ℕ) [Fact p.Prime], (p : 𝓞 K) ∈ pl.asIdeal → ∀ (T : CDVR) (io : K →+* T.Fr) (e : ℕ), OverLa pl T.V io e → T.FinRes → ∃ jm : T.Fr →+* ℂ_[p], ∀ z : T.Fr, z ≠ 0 → ‖jm z‖ = (p : ℝ) ^ (-((vV T.V z : ℝ) / (vV T.V (io (p : K)) : ℝ))) := by
  first | exact @GlobalTheory.EmbedReadsValuation.exists_embedding_norm_eq | exact GlobalTheory.EmbedReadsValuation.exists_embedding_norm_eq | (intros; apply GlobalTheory.EmbedReadsValuation.exists_embedding_norm_eq <;> assumption)
