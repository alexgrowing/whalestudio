import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsCechNerveQuasiIsoOfSmoothSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chains_cechNerve_quasiIso_of_smooth_surjective : ∀ (R : Type) [CommRing R] {Y X : Scheme.{0}} (f : Y ⟶ X) [Smooth f] [Surjective f], QuasiIso ((chains R).map (cechAug f)) := by
  first | exact @GlobalTheory.EtC.chains_cechAug_quasiIso_of_smooth | exact GlobalTheory.EtC.chains_cechAug_quasiIso_of_smooth | (intros; apply GlobalTheory.EtC.chains_cechAug_quasiIso_of_smooth <;> assumption)
