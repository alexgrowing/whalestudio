import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValTorusPointAndTranslate
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsTor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem gtCoord_overPoint_ext {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (a a' : Z ⟶ thickObj R I e G)
    (hp : a.left ≫ g.pG.left = a'.left ≫ g.pG.left)
    (hv : ∀ (z : Z.left) (J : (Z.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
      ∀ χ : D.X, val (g.t χ) a.left z J = val (g.t χ) a'.left z J) : a = a' := by
  have := g.i_hom
  have := g.q_hom
  have hq : a ≫ g.q = a' ≫ g.q := by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    exact (Category.assoc _ _ _).trans (hp.trans (Category.assoc _ _ _).symm)
  have hd : (a' * a⁻¹) ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hq, mul_inv_cancel]
    rfl
  let τ := g.isKernel.lift (a' * a⁻¹) (toUnit _) hd
  have hτ : τ ≫ g.i = a' * a⁻¹ := g.isKernel.lift_fst _ _ _
  have h1 : τ = 1 := by
    refine TorusPts.torusPt_ext fun χ => ?_
    refine congrArg Units.val (show pullU τ.left ⊤ (charUnit _ D.X χ) =
      pullU (1 : Z ⟶ splitTorus _ D.X).left ⊤ (charUnit _ D.X χ) from unit_ext fun z _ => ?_)
    choose J hJ using fun ψ : Z.left ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
    have k := (TorusCoord.val_torus_point_and_translate R I D e G g Z τ a z J hJ χ).2
    have k' := (TorusCoord.val_torus_point_and_translate R I D e G g Z 1 a z J hJ χ).2
    rw [hτ, inv_mul_cancel_right] at k
    rw [MonObj.one_comp, _root_.one_mul] at k'
    have k2 := mul_right_cancel (k.symm.trans ((hv z J hJ χ).symm.trans k'))
    exact (gm_pull (𝟙 Z.left) τ.left z ⊤ trivial _).trans (k2.trans
      (gm_pull (𝟙 Z.left) (1 : Z ⟶ splitTorus _ D.X).left z ⊤ trivial _).symm)
  rw [h1, MonObj.one_comp] at hτ
  exact (mul_inv_eq_one.1 hτ.symm).symm

theorem gtCoord_point_ext : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) {Z : Scheme.{0}} (r r' : Z ⟶ (thickObj R I e G).left), r ≫ (thickObj R I e G).hom = r' ≫ (thickObj R I e G).hom → r ≫ g.pG.left = r' ≫ g.pG.left → (∀ (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → ∀ χ : D.X, val (g.t χ) r z J = val (g.t χ) r' z J) → r = r' := by
  intro R _ _ I D e G _ _ g Z r r' hb hp hv
  let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    Over.mk (r ≫ (thickObj R I e G).hom)
  exact congrArg (fun φ => φ.left) (gtCoord_overPoint_ext g (Z := FinalForm) (Over.homMk r rfl) (Over.homMk r' hb.symm) hp hv)

end GlobalTheory.Mum
