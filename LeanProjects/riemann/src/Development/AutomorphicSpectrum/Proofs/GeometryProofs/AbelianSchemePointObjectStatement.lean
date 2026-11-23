import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObject
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_point_object : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (f : X ⟶ Y.X) (t : SAB H X) (_ : SABMap t Y.t f) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (x : Sp Ω ⟶ Xo.XF c), ξ ≫ f = x ≫ Y.j → ∃ (s : Sp Ω ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s), Nonempty (SABMap o.t t ξ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ObjAt.exists_obj_at | exact GlobalTheory.CompanionTheory.Ar.ObjAt.exists_obj_at | (intros; apply GlobalTheory.CompanionTheory.Ar.ObjAt.exists_obj_at <;> assumption)
