import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreEmbeddingLiftSeparatedFiniteTypeQuasi
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedFibreEmbedding_lift_separated_finiteType_quasiCompact : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', IsSeparated (pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over) ∧ LocallyOfFiniteType (pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over) ∧ QuasiCompact (pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over) := by
  first | exact @GlobalTheory.Mum.emb_lift_sep_loft_qc | exact GlobalTheory.Mum.emb_lift_sep_loft_qc | (intros; apply GlobalTheory.Mum.emb_lift_sep_loft_qc <;> assumption)
