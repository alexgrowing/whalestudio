import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelAcyclic
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_cech_level_eq_zero_of_pos : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ) (m : ℕ), 0 < m → ∀ y : H R (disc.obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op (SimplexCategory.mk (k))))) F m, y = 0 := by
  first
  | exact @GlobalTheory.EtC.cech_level_acyclic
  | exact GlobalTheory.EtC.cech_level_acyclic
  | (intros; apply GlobalTheory.EtC.cech_level_acyclic <;> assumption)
