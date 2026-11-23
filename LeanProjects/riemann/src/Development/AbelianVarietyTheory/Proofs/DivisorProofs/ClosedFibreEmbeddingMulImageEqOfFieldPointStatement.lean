import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreEmbeddingMulImageEqOfFieldPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedFibre_embedding_mul_image_eq_of_field_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → ∀ (Ω : Type) [Field Ω] (κ : ResidueField R →+* Ω) (s : Sp Ω ⟶ M.S) (a b c : Sp Ω ⟶ N.U.left) (x y : Over.mk s ⟶ G'), s ≫ M.π = spMap (κ.comp (residue R)) → N.Pt s a x.left → N.Pt s b y.left → N.Pt s c (x * y).left → ∃ (Ω' : Type) (_ : Field Ω') (io : Ω →+* Ω') (ca cb : Over.mk (spMap (io.comp κ)) ⟶ E.Y), ca.left ≫ E.j = spMap io ≫ a ≫ fU ∧ cb.left ≫ E.j = spMap io ≫ b ≫ fU ∧ (ca * cb).left ≫ E.j = spMap io ≫ c ≫ fU := by
  first | exact @GlobalTheory.Mum.closed_product_image | exact GlobalTheory.Mum.closed_product_image | (intros; apply GlobalTheory.Mum.closed_product_image <;> assumption)
