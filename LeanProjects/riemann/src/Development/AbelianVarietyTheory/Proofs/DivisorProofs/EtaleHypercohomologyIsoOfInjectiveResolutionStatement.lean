import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHypercohomologyIsoOfInjectiveResolution
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHypercohomology_iso_of_injective_resolution : ∀ (R : Type) [CommRing R] (M : Shv R) (C : Cx R) (ε : sgl M ⟶ C), C.IsStrictlyGE 0 → (∀ t, Injective (C.X t)) → QuasiIso ε → ∀ (K : Cx R) (n : ℤ), Nonempty (HK R K M n ≃+ CohomologyClass K C n) := by
  first | exact @GlobalTheory.EtC.InjResCmp.hyper_iso_of_injective_resolution | exact GlobalTheory.EtC.InjResCmp.hyper_iso_of_injective_resolution | (intros; apply GlobalTheory.EtC.InjResCmp.hyper_iso_of_injective_resolution <;> assumption)
