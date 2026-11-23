import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringsRefineOfCechConerveProperty
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coveringsRefine_of_cechConerve_property : ∀ (T : Type 1) [Category.{0} T] [HasFiniteWidePushouts T] (Cov : MorphismProperty T) (Q : ∀ (U : T) (X : CosimplicialObject T), ((CosimplicialObject.const T).obj U ⟶ X) → Prop), (∀ (U V : T) (g : U ⟶ V), Cov g → Q U _ (coAug g)) → Refines Cov Q := by
  first | (exact @GlobalTheory.refines_of_coAug) | (exact GlobalTheory.refines_of_coAug) | (intros; apply GlobalTheory.refines_of_coAug  <;> assumption)
