import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreProductCoordinateIndependent
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedFibre_product_coordinate_independent : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → Surjective M.π → ∀ (Ω : Type) [Field Ω] (κ : ResidueField R →+* Ω) (s s' : Sp Ω ⟶ M.S) (a b c c' : Sp Ω ⟶ N.U.left) (x y : Over.mk s ⟶ G') (x' y' : Over.mk s' ⟶ G'), s ≫ M.π = spMap (κ.comp (residue R)) → s' ≫ M.π = spMap (κ.comp (residue R)) → N.Pt s a x.left → N.Pt s b y.left → N.Pt s c (x * y).left → N.Pt s' a x'.left → N.Pt s' b y'.left → N.Pt s' c' (x' * y').left → c = c' := by
  first | exact @GlobalTheory.Mum.Near.closed_product_unique | exact GlobalTheory.Mum.Near.closed_product_unique | (intros; apply GlobalTheory.Mum.Near.closed_product_unique <;> assumption)
