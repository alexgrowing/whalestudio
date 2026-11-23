import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd

open Formalism.BasicNotions Formalism.L2.Col GlobalTheory.Mem

namespace GlobalTheory.Mem.Col2

theorem fOk_of_fieldsOk {X : Fields} (hX : X.Ok) (σ : X.K →+* ℂ) (hσ : ∀ x, σ (star x) = starRingEnd ℂ (σ x)) :
    FOk X.emb σ :=
  ⟨hX.conjE, hX.emb_star, hσ⟩

theorem base_fOk (B : Base) : letI := B.fields.starE; FOk B.fields.emb B.embLL :=
  fOk_of_fieldsOk (GlobalTheory.Mem.FieldsLaws.fields_ok B) B.embLL B.starLL_cx

theorem base_fields_primes_ok : ∀ (B : Base) (X : PreX B.toPre),
    B.fields.Ok ∧ (B.primes X).Ok ∧ B.wts.Ok ∧ (letI := B.host.cmStar; FOk B.tauLL B.embLL) ∧
      2 * B.fields.f * B.R.k < (B.primes X).g 0 - 1 := fun B X =>
  ⟨GlobalTheory.Mem.FieldsLaws.fields_ok B, (GlobalTheory.BasePrimes.primes_ok B X).1, B.wts_isOk, base_fOk B,
    (B.primes_sizes X).g_big 0⟩

example (B : Base) (X : PreX B.toPre) : letI := B.fields.starE; FOk B.fields.emb B.embLL :=
  (base_fields_primes_ok B X).2.2.2.1

end GlobalTheory.Mem.Col2
