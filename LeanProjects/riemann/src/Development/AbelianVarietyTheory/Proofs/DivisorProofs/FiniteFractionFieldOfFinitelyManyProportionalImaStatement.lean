import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFractionFieldOfFinitelyManyProportionalIma
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_fractionField_of_finitely_many_proportional_images : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (X : Scheme.{0}) (x : Sp R ⟶ X) (I : Type) [Finite I] (v : I → R), R.FG → (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) → ((spMap R.val.toRingHom ≫ x).stalkMap (genericPoint (Sp Ω))).hom.Finite → (∀ (K : Type) [Field K] [IsAlgClosed K] (c : I → K), Set.Finite {y : Sp K ⟶ X | ∃ σ : R →+* K, spMap σ ≫ x = y ∧ ∃ u : K, u ≠ 0 ∧ ∀ i, σ (v i) = u * c i}) → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {z | ∃ i i', z = (v i : Ω) / (v i' : Ω)})) Ω := by
  first | exact @GlobalTheory.LevelFinite.finite_ratio_field | exact GlobalTheory.LevelFinite.finite_ratio_field | (intros; apply GlobalTheory.LevelFinite.finite_ratio_field <;> assumption)
