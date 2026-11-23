import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharactersPrescribedValues
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
import Formalism.LocalToGlobal.Columns.BaseLemmas
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_characters_prescribed_values : ∀ (B : Base) (X : PreX B.toPre) (mu : Fin B.R.m → HeightOneSpectrum (𝓞 B.host.E) → B.LLˣ) (eta : HeightOneSpectrum (𝓞 B.host.E) → B.LLˣ), ∃ Ch : Chars B.fields (B.primes X) B.R.m, Ch.Ok ∧ Ch.muVal = mu ∧ Ch.etaVal = eta := by
  first | exact @GlobalTheory.BaseChars.exists_chars | exact GlobalTheory.BaseChars.exists_chars | (intros; apply GlobalTheory.BaseChars.exists_chars <;> assumption)
