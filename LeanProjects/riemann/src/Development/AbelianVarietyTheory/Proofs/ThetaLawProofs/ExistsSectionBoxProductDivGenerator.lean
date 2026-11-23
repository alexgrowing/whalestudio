import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.KeyQuot

open TopologicalSpace Opposite

theorem gs_prod {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {K : Type} [Fintype K]
    (a : K → Γ(X, U)) : gs f y U (∏ k, a k) = ∏ k, gs f y U (a k) := by
  simp only [gs_eq f y U h, map_prod]

theorem exists_boxSec {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (th : L.Sec) :
    ∃ t : LB.Sec (LB.LinComb L φ (fun _ => 1)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J, Good L z J →
      sval t r z J = ∏ k, gs (r ≫ φ k) z (L.U (J (r ≫ φ k))) (th.f (J (r ≫ φ k))) := by
  have l : ∀ (j : K → L.ι) (k : K), LB.wchart L φ j ≤ φ k ⁻¹ᵁ L.U (j k) :=
    fun _ k _ hy => Set.mem_iInter.1 hy k
  let a : ∀ j : K → L.ι, Γ(Y, LB.wchart L φ j) := fun j =>
    ∏ k, (Y.presheaf.map (homOfLE (l j k)).op).hom (((φ k).app (L.U (j k))).hom (th.f (j k)))
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L φ j →
      gs r z (LB.wchart L φ j) (a j) = ∏ k, gs (r ≫ φ k) z (L.U (j k)) (th.f (j k)) := fun Z r z j hj =>
    (gs_prod r z _ hj _).trans (Finset.prod_congr rfl fun k _ =>
      (gs_res r z (l j k) hj _).trans (gs_pull r (φ k) z _ (l j k hj) _))
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z J hJ => v Z r z _ (hJ.mem φ r)⟩
  refine ((gs_res (𝟙 Y) y _ hy _).trans (v _ _ y j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
      (congrArg Units.val (gm_linComb L φ _ (𝟙 Y) y j j' hy.1 hy.2)))
      ((gs_res (𝟙 Y) y _ hy _).trans (v _ _ y j' hy.2)))).symm)
  rw [Units.coe_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [zpow_one]
  exact gs_compat th (𝟙 Y ≫ φ k) y (l j k hy.1) (l j' k hy.2)

theorem exists_sec_quot : ∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ : K₁ → (Y ⟶ X)) (ψ : K₂ → (Y ⟶ X)) (e : ℤ) (th : L.Sec) (w : LB.Gen (LB.LinComb L (K := K₁ ⊕ K₂) (Sum.elim φ ψ) (Sum.elim (fun _ => 1) (fun _ => -e)))), w.IsGen → ∃ s : LB.Sec (LB.LinComb L ψ (fun _ => e)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J, Good L z J → ∏ k, gs (r ≫ φ k) z (L.U (J (r ≫ φ k))) (th.f (J (r ≫ φ k))) = (val w r z J).val * sval s r z J := by
  intro X Y L hL K₁ K₂ _ _ φ ψ e th w hw
  obtain ⟨t, ht⟩ := exists_boxSec L φ th
  have hu := DVR.invGen_isGen _ _ _ _ hw
  obtain ⟨s, hs⟩ := exists_sec hL (φ' := ψ) (ε' := fun _ => e) (by
    intro U _ h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Category.id_comp, zpow_one,
      zpow_neg, Finset.prod_inv_distrib, mul_inv, mul_inv_cancel_left, inv_inv]) (pullMulSec t (𝟙 Y) _ hu)
  refine ⟨s, fun Z r z J hJ => ?_⟩
  rw [hs Z r z J hJ, sval_pullMulSec t (𝟙 Y) _ hu r z hJ, Category.comp_id, ht Z r z J hJ, val_inv,
    mul_left_comm, Units.mul_inv, _root_.mul_one]

end GlobalTheory.KeyQuot
