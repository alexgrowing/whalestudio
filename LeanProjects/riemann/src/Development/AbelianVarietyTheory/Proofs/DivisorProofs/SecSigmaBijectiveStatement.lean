import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecSigmaBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sec_sigma_res_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) {ι : Type} (V : ι → Scheme.{0}), Function.Bijective fun (a : Sec F (∐ V)) (i : ι) => Sec.res (Sigma.ι V i) a := by
  first | (exact @GlobalTheory.EtC.sec_sigma_bijective) | (exact GlobalTheory.EtC.sec_sigma_bijective) | (intros; apply GlobalTheory.EtC.sec_sigma_bijective  <;> assumption)
