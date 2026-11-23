import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem refines_of_coAug : ∀ (T : Type 1) [Category.{0} T] [HasFiniteWidePushouts T] (Cov : MorphismProperty T) (Q : ∀ (U : T) (X : CosimplicialObject T), ((CosimplicialObject.const T).obj U ⟶ X) → Prop), (∀ (U V : T) (g : U ⟶ V), Cov g → Q U _ (coAug g)) → Refines Cov Q := by
  intro T _ _ Cov Q hQ U V g hg
  refine ⟨_, coAug g, WidePushout.ι (fun _ : Fin 1 => g) 0, ?_, hQ U V g hg⟩
  exact WidePushout.arrow_ι (fun _ : Fin 1 => g) 0

end GlobalTheory
