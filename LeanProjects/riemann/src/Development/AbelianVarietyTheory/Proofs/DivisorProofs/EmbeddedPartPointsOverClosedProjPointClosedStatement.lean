import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddedPartPointsOverClosedProjPointClosed
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeddedPart_points_over_closedProjPoint_closed : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → ∀ (G' : Over S) [GrpObj G'], Smooth G'.hom → ∀ (E : Emb π G') (H' : E.H.toScheme.Opens) (X : Scheme.{0}) (o : H'.toScheme ⟶ X) (g : X ⟶ PSpace R E.N), IsSeparated g → o ≫ g = H'.ι ≫ E.f → (∀ z : E.H.toScheme, π (G'.hom (E.H.ι z)) = closedPoint R → z ∈ H') → ∀ w : PSpace R E.N, PSpace.str R E.N w = closedPoint R → ∃ C : Set X, IsClosed C ∧ C ∩ g ⁻¹' {w} = Set.range o ∩ g ⁻¹' {w} := by
  first | exact @GlobalTheory.Mum.FibClosed.range_inter_fibre_closed | exact GlobalTheory.Mum.FibClosed.range_inter_fibre_closed | (intros; apply GlobalTheory.Mum.FibClosed.range_inter_fibre_closed <;> assumption)
