import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivOfLocallyConstantBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomologyEquiv_of_locallyConstant_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (g : Sec F S), Gen F S g → ∀ (U U' : Scheme.{0}) (s : U ⟶ S) (f : U' ⟶ U), AcycF R (sch.obj U) F → AcycF R (sch.obj U') F → Function.Bijective (fun φ : LocallyConstant U R => φ.comap f.base.hom) → Eqv R (sch.map f) F := by
  first | exact @GlobalTheory.EtC.eqv_of_gen_lc | exact GlobalTheory.EtC.eqv_of_gen_lc | (intros; apply GlobalTheory.EtC.eqv_of_gen_lc <;> assumption)
