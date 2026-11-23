import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieCoordinatesOnFieldFibresLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lie_coordinates_on_field_fibres_local_ring : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∃ (n : ℕ) (M : (G ⟶ G) → Matrix (Fin n) (Fin n) R), (∀ g : ℕ, SmoothOfRelativeDimension g G.hom → n = g) ∧ ∀ (k : Type) [Field k] (f : R →+* k), ∃ T : (Fin n → k) → (epsPt (spMap f) ⟶ G), Function.Injective T ∧ (∀ v : epsPt (spMap f) ⟶ G, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (v).left = (1 : Over.mk (spMap f) ⟶ G).left ↔ v ∈ Set.range T) ∧ (∀ c c', T (c + c') = T c * T c') ∧ (∀ (t : k) c, (T (t • c)).left = spMap (epsScale t) ≫ (T c).left) ∧ ∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map f).mulVec c) := by
  first | exact @GlobalTheory.exists_lie_coordinates_fibres | exact GlobalTheory.exists_lie_coordinates_fibres | (intros; apply GlobalTheory.exists_lie_coordinates_fibres <;> assumption)
