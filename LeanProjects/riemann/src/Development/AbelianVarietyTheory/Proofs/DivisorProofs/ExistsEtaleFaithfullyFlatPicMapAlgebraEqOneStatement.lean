import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFaithfullyFlatPicMapAlgebraEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_faithfullyFlat_picMapAlgebra_eq_one : ∀ (A : Type) [CommRing A] (c : CommRing.Pic A), ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra.Etale A B) (_ : Module.FaithfullyFlat A B), CommRing.Pic.mapAlgebra A B c = 1 := by
  first | (exact @GlobalTheory.PicLoc.exists_etale_faithfullyFlat_mapAlgebra_eq_one) | (exact GlobalTheory.PicLoc.exists_etale_faithfullyFlat_mapAlgebra_eq_one) | (intros; apply GlobalTheory.PicLoc.exists_etale_faithfullyFlat_mapAlgebra_eq_one  <;> assumption)
