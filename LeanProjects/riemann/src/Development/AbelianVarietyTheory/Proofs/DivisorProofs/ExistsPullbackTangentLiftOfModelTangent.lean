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

noncomputable section
namespace GlobalTheory.TanLiftPull

theorem toUnit_left_eq {S : Scheme.{0}} (A : Over S) (f : A ⟶ 𝟙_ (Over S)) : f.left = A.hom := by
  simpa using Over.w f

theorem one_left_eq {S : Scheme.{0}} (A : Over S) (G : Over S) [GrpObj G] :
    (1 : A ⟶ G).left = A.hom ≫ η[G].left := by
  rw [← toUnit_left_eq A (toUnit A)]
  rfl

theorem exists_isTan_lift : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {V : Type} [CommRing V] (x : Sp V ⟶ Y.X) (G : SAB H (Sp V)) (ψ : SABMap G Y.t x) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G), ∃ w : epsOver V V ⟶ G.G, IsTan w ∧ (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w.left ≫ ψ.φ := by
  intro E _ _ _ H Dw l Xo c O _ β Y V _ x G ψ v
  have hpb : IsPullback ψ.φ G.G.hom Y.t.G.hom x := ψ.cart.1
  have hsq : (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left ≫ Y.t.G.hom = (epsOver V V).hom ≫ x := by
    rw [Over.w]; rfl
  have hfa : spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ spMap (algebraMap V (DualNumber V)) = 𝟙 _ := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert Spec.map_id (CommRingCat.of V)
    ext a
    simp
  refine ⟨Over.homMk (hpb.lift _ _ hsq) (hpb.lift_snd _ _ _), ?_, (hpb.lift_fst _ _ _).symm⟩
  show spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ hpb.lift _ _ hsq = (1 : ptOver V V ⟶ G.G).left
  apply hpb.hom_ext
  · rw [Category.assoc, hpb.lift_fst]
    have h1 := congrArg (fun f => f.left) (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem v)
    simp only [smT_left] at h1
    have key : spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ spMap (epsMul (0 : V)) =
        spMap (TrivSqZeroExt.fstHom V V V).toRingHom := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext <;> simp [epsMul]
    have hunit : η[G.G].left ≫ ψ.φ = x ≫ η[Y.t.G].left := by
      have h := ψ.cm.e_comm
      rw [ψ.base] at h
      exact h
    rw [← key, Category.assoc, h1, one_left_eq, one_left_eq, Category.assoc, hunit]
    simp only [Over.mk_hom, ← Category.assoc, hfa]
    simp [spMap]
  · rw [Category.assoc, hpb.lift_snd, Over.w]
    simp only [Over.mk_hom]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2

end GlobalTheory.TanLiftPull
