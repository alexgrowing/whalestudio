import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TanPull

theorem one_left_congr {X Z : Scheme.{0}} {G : Over X} [GrpObj G] {f g : Z ⟶ X} (h : f = g) :
    (1 : Over.mk f ⟶ G).left = (1 : Over.mk g ⟶ G).left := by
  subst h; rfl

theorem isTanAtG_comp
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
    {V : Type} [CommRing V] (x : Sp V ⟶ Y.X) (G : SAB H (Sp V)) (ψ : SABMap G Y.t x)
    (w : epsOver V V ⟶ G.G) (hw : IsTan w) : IsTanAtG Y.t x (w.left ≫ ψ.φ) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, ψ.cart.1.w, ← Category.assoc, Over.w w]
    rfl
  · rw [← Category.assoc, hw]
    refine (Formalism.L2.Pj.grpPull_one ψ.cart (ptOver V V)).symm.trans (one_left_congr ?_)
    show spMap (algebraMap V V) ≫ x = x
    have : spMap (algebraMap V V) = 𝟙 _ := by
      rw [Algebra.algebraMap_self]; exact Spec.map_id _
    rw [this, Category.id_comp]

theorem exists_tanM_of_isTan
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
    {V : Type} [CommRing V] (x : Sp V ⟶ Y.X) (G : SAB H (Sp V)) (ψ : SABMap G Y.t x)
    (w : epsOver V V ⟶ G.G) (hw : IsTan w) :
    ∃ v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G, (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w.left ≫ ψ.φ :=
  ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT (Formalism.L2.Pj.ovT (isTanAtG_comp x G ψ w hw)) (Formalism.L2.Pj.smT_zero_ovT _), rfl⟩

end GlobalTheory.TanPull
