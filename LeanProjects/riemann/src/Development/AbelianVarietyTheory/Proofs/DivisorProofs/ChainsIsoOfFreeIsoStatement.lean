import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsIsoOfFreeIso
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
theorem _root_.GlobalTheory.T.chains_iso_of_free_iso : ∀ (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E'), (∀ n, IsIso ((free R).map (f.app n))) → IsIso ((chains R).map f) := by
  first | exact @GlobalTheory.EtC.isIso_chains_map_of_isIso_free | exact GlobalTheory.EtC.isIso_chains_map_of_isIso_free | (intros; apply GlobalTheory.EtC.isIso_chains_map_of_isIso_free <;> assumption)
