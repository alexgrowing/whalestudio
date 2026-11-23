import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleQuasiSectionOfSmoothSchemeHom
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_quasiSection_of_smooth_scheme_hom : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) [Smooth f] (x : X), x ∈ Set.range f → ∃ (V : Scheme.{0}) (s : V ⟶ Y), Etale (s ≫ f) ∧ x ∈ Set.range (s ≫ f) := by
  first | exact @GlobalTheory.exists_etale_quasiSection_of_smooth | exact GlobalTheory.exists_etale_quasiSection_of_smooth | (intros; apply GlobalTheory.exists_etale_quasiSection_of_smooth <;> assumption)
