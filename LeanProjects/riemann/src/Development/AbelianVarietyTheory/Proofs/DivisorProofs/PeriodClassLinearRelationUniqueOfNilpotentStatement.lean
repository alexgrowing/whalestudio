import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassLinearRelationUniqueOfNilpotent
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodClass_linear_relation_unique_of_nilpotent : ∀ {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam Empty g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (et : Hol F₀.V →+* R) (M : Ideal R), K₀.Rich → (∀ z, z ∈ F₀.V) → IsNilpotent M → (∀ (f : Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) → ∀ {io : Type} (S : Finset io) (d : io → R) (q : io → (Λ →+ R)) (q' : Λ →+ R), K₀.perClD et M q' = ∑ i ∈ S, d i • K₀.perClD et M (q i) → ∀ l, q' l = ∑ i ∈ S, d i * q i l := by
  first | exact @GlobalTheory.AnPer.perClD_relation_unique | exact GlobalTheory.AnPer.perClD_relation_unique | (intros; apply GlobalTheory.AnPer.perClD_relation_unique <;> assumption)
