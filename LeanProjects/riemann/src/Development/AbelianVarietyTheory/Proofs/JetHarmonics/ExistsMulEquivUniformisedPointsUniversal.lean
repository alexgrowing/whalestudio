import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PtTie

theorem exists_mulEquiv_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (Z : Over S') :
    ∃ e : (Z ⟶ G') ≃* (Over.mk (Z.hom ≫ f) ⟶ G), ∀ x, (e x).left = x.left ≫ φ := by
  let Φ₀ : (Z ⟶ G') → (Over.mk (Z.hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      show (x.left ≫ φ) ≫ G.hom = Z.hom ≫ f
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x])
  let Φ : (Z ⟶ G') →ₙ* (Over.mk (Z.hom ≫ f) ⟶ G) :=
    ⟨Φ₀, fun x y => Over.OverMorphism.ext (h.2 Z x y (Φ₀ x) (Φ₀ y) rfl rfl).symm⟩
  have hinj : Function.Injective Φ := fun x y hxy =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg CommaMorphism.left hxy) (by rw [Over.w x, Over.w y]))
  have hsurj : Function.Surjective Φ := fun x₀ =>
    ⟨Over.homMk (h.1.lift x₀.left Z.hom (Over.w x₀)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  exact ⟨MulEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun x => rfl⟩

open scoped CategoryTheory.Obj in

theorem exists_mulEquiv_ptTieF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (F : Type) [Field F] [Algebra T.Fr F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) → ∃ e : (TFK (R := T.V) F ⟶ P.A.A) ≃* (ptO Xo xF ⟶ Xo.univ.t.G), (∀ x b, PtTieF I P F xF x b ↔ b = e x) ∧ ∀ (a : 𝓞 E) x, e (x ≫ P.oA.act a) = e x ≫ Xo.univ.t.act.act a := by
  intro E _ _ _ H Dw l Xo c T io y I P F _ _ xF hxF
  letI := H.starRing
  subst hxF
  have := P.U.gen_hom
  have gpG : IsGrpPullback P.A.A I.G.G (jK T.V) (P.U.gen.inv.left ≫ pullback.fst I.G.G.hom (jK T.V)) := by
    have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback I.G.G (jK T.V))).congr
      (Category.id_comp _) rfl
  have actA : ∀ a, (P.oA.act a).left ≫ P.U.gen.inv.left ≫ pullback.fst I.G.G.hom (jK T.V) =
      P.U.gen.inv.left ≫ pullback.fst I.G.G.hom (jK T.V) ≫ (I.G.act.act a).left := by
    intro a
    have e : P.oA.act a ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK T.V)).map (I.G.act.act a) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext a)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  obtain ⟨eA, hA⟩ := exists_mulEquiv_of_isGrpPullback gpG (TFK (R := T.V) F)
  obtain ⟨e2, h2⟩ := exists_mulEquiv_of_isGrpPullback I.m2.cart (TFK (R := T.V) F)
  obtain ⟨e1, h1⟩ := exists_mulEquiv_of_isGrpPullback I.m1.cart (TFK (R := T.V) F)
  refine ⟨(eA.trans e2.symm).trans e1, fun x b => ⟨?_, ?_⟩, fun a x => ?_⟩
  · rintro ⟨r, hr, hr1, hr2⟩
    let r' : TFK (R := T.V) F ⟶ I.t'.G := Over.homMk r hr
    have h3 : e2 r' = eA x := Over.OverMorphism.ext (by
      rw [h2, hA]
      exact hr2.trans (by rw [Over.comp_left, Category.assoc]))
    show b = e1 (e2.symm (eA x))
    rw [← h3, e2.symm_apply_apply]
    exact Over.OverMorphism.ext (hr1.symm.trans (h1 r').symm)
  · rintro rfl
    refine ⟨(e2.symm (eA x)).left, Over.w _, (h1 _).symm, ?_⟩
    refine (h2 _).symm.trans ?_
    rw [e2.apply_symm_apply, hA, Over.comp_left, Category.assoc]
  · have h3 : e2.symm (eA (x ≫ P.oA.act a)) = e2.symm (eA x) ≫ I.t'.act.act a := by
      rw [MulEquiv.symm_apply_eq]
      apply Over.OverMorphism.ext
      rw [hA, h2, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, actA, I.m2.act a,
        ← Category.assoc _ I.m2.cm.F, ← h2, e2.apply_symm_apply, hA, Category.assoc, Category.assoc]
    show e1 (e2.symm (eA (x ≫ P.oA.act a))) = e1 (e2.symm (eA x)) ≫ Xo.univ.t.act.act a
    rw [h3]
    apply Over.OverMorphism.ext
    rw [h1, Over.comp_left, Over.comp_left, h1, Category.assoc, Category.assoc, I.m1.act a]

end GlobalTheory.PtTie
