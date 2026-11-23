import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTypePrimeUnderEq
import Mathlib
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubOneMemMapOfEq
open NumberField IsDedekindDomain Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_typePrime_under_eq : ∀ (X : Fields) (Pr : Primes X), X.Ok → Pr.Ok → ∀ (i : Fin 2) (P : HeightOneSpectrum (𝓞 X.E)), ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal → ∃ P' ∈ Pr.vG i, P'.under (𝓞 X.F) = P.under (𝓞 X.F) := by
  first | exact @GlobalTheory.GprimUnder.exists_vG_under | exact GlobalTheory.GprimUnder.exists_vG_under | (intros; apply GlobalTheory.GprimUnder.exists_vG_under <;> assumption)
