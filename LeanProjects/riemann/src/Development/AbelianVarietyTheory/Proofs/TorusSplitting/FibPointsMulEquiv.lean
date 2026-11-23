import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.EtaVal

theorem exists_mulEquiv_points {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    ∃ tr : (Over.mk (T.hom ≫ f) ⟶ G) ≃* (T ⟶ G'), (∀ p, (tr p).left ≫ φ = p.left) ∧
      ∀ (a : G ⟶ G) (a' : G' ⟶ G'), a'.left ≫ φ = φ ≫ a.left → ∀ p, tr (p ≫ a) = tr p ≫ a' := by
  have hl : ∀ x : T ⟶ G', (pushHom h T x).left = x.left ≫ φ := fun _ => rfl
  have hinj : ∀ x y : T ⟶ G', x.left ≫ φ = y.left ≫ φ → x = y := fun x y e =>
    Over.OverMorphism.ext (h.1.hom_ext e ((Over.w x).trans (Over.w y).symm))
  have hb : Function.Bijective (pushHom h T) := by
    refine ⟨fun x y e => hinj x y (by rw [← hl, ← hl, e]), fun p => ?_⟩
    refine ⟨Over.homMk (h.1.lift p.left T.hom (Over.w p)) (h.1.lift_snd _ _ _), ?_⟩
    exact Over.OverMorphism.ext ((hl _).trans (h.1.lift_fst _ _ _))
  have key : ∀ p, ((MulEquiv.ofBijective _ hb).symm p).left ≫ φ = p.left := fun p =>
    (hl _).symm.trans (congrArg (fun z => z.left) ((MulEquiv.ofBijective _ hb).apply_symm_apply p))
  refine ⟨(MulEquiv.ofBijective _ hb).symm, key, fun a a' e p => hinj _ _ ?_⟩
  rw [key, Over.comp_left, Over.comp_left, Category.assoc, e, ← Category.assoc, key]

theorem fib_points_mulEquiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (R : Type) [CommRing R] [IsDomain R] [CharZero R] (x : Sp (FractionRing R) ⟶ Xo.X) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (Φ : Fib Xo x A) (F : Type) [Field F] [Algebra (FractionRing R) F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap (FractionRing R) F) ≫ x → ∃ tr : (ptO Xo xF ⟶ Xo.univ.t.G) ≃* (TFK (R := R) F ⟶ A.A), (∀ p, (tr p).left ≫ Φ.φ = p.left) ∧ ∀ (a : Xo.univ.t.G ⟶ Xo.univ.t.G) (a' : A.A ⟶ A.A), a'.left ≫ Φ.φ = Φ.φ ≫ a.left → ∀ p, tr (p ≫ a) = tr p ≫ a' := by
  intro E _ _ _ H Dw l Xo R _ _ _ x A Φ F _ _ xF hx
  subst hx
  exact exists_mulEquiv_points Φ.cart (TFK (R := R) F)

end GlobalTheory.EtaVal
