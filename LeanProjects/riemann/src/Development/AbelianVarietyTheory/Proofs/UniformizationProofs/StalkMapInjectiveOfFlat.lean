import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftTest

theorem stalkMap_injective_of_flat {W Z : Scheme.{0}} (f : W ⟶ Z) [Flat f] (w : W) :
    Function.Injective (f.stalkMap w).hom := by
  have h := Flat.stalkMap f w
  algebraize [(f.stalkMap w).hom]
  have : IsLocalHom (algebraMap (Z.presheaf.stalk (f w)) (W.presheaf.stalk w)) := f.toLRSHom.prop w
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Z.presheaf.stalk (f w)) (B := W.presheaf.stalk w)
  exact FaithfulSMul.algebraMap_injective (Z.presheaf.stalk (f w)) (W.presheaf.stalk w)

theorem gs_comp {W Z Y : Scheme.{0}} (f : W ⟶ Z) (r : Z ⟶ Y) (w : W) (U : Y.Opens) (h : r (f w) ∈ U)
    (a : Γ(Y, U)) : gs (f ≫ r) w U a = (f.stalkMap w).hom (gs r (f w) U a) := by
  rw [← gs_pull f r w U h, gs_eq f w (r ⁻¹ᵁ U) h, gs_eq r (f w) U h]
  exact (Scheme.Hom.germ_stalkMap_apply f (r ⁻¹ᵁ U) w h _).symm

theorem sval_eq_zero_of_flat {X Y Z W : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (d : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (f : W ⟶ Z) [Flat f] (w : W)
    (h : ∀ J, Good L w J → sval d (f ≫ r) w J = 0) (J) (hJ : Good L (f w) J) : sval d r (f w) J = 0 := by
  choose I hI using fun χ : W ⟶ X => exists_chart hL (χ w)
  have hm : r (f w) ∈ LB.wchart L φ (fun k => J (r ≫ φ k)) := hJ.mem φ r
  have e := sec_trans d (f ≫ r) w (j := fun k => J (r ≫ φ k)) hm (Good.mem hI φ (f ≫ r))
  have e0 : gs (f ≫ r) w (LB.wchart L φ (fun k => I ((f ≫ r) ≫ φ k))) (d.f (fun k => I ((f ≫ r) ≫ φ k))) = 0 := h I hI
  rw [e0, mul_zero] at e
  exact (map_eq_zero_iff _ (stalkMap_injective_of_flat f w)).1 ((gs_comp f r w _ hm _).symm.trans e)

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (Y : Over (Spec (CommRingCat.of R))) (p : Y ⟶ D.P.A) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (Y.left ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε)), (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good L z J → sval d r z J = 0) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.left), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ Y.hom) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0 := by
  intro R _ _ I D e G _ _ g Y p X L hL K _ φ ε d H Z r ⟨ρ, hρ⟩ z J hJ
  have := g.q_flat
  have := g.q_surj
  let b : Z ⟶ (thickObj R I e D.P.A).left :=
    pullback.lift (r ≫ p.left) ρ (by rw [Category.assoc, Over.w p, hρ])
  have hb : b ≫ pullback.fst D.P.A.hom (thick R I e) = r ≫ p.left := pullback.lift_fst _ _ _
  obtain ⟨w, rfl⟩ := (pullback.fst b g.q.left).surjective z
  refine sval_eq_zero_of_flat hL d r (pullback.fst b g.q.left) w (fun J' hJ' => ?_) J hJ
  refine H _ (pullback.snd b g.q.left) _ ?_ w J' hJ'
  rw [Category.assoc, ← hb, pullback.condition_assoc]
  rfl

end GlobalTheory.LiftTest
