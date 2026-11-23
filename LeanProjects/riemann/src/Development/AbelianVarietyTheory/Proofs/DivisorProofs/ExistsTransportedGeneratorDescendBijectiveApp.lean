import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralOfTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDescendThrough

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.UU GlobalTheory.UU.PackageDescent

noncomputable section
namespace GlobalTheory.Mum.BijDescent

variable {X X' Y Y' : Scheme.{0}} {K : Type} [Fintype K]

theorem exists_gen_descend_val_bij {L : LB X} (π : Y' ⟶ Y)
    (hπ : ∀ V : Y.Opens, Function.Bijective (π.app V).hom) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (u : LB.Gen (LB.LinComb L (fun k => π ≫ φ k) ε)) (hu : u.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J → val t (r ≫ π) z J = val u r z J := by
  have le : ∀ j : K → L.ι, π ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => π ≫ φ k) j :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have desc : ∀ j : K → L.ι, ∃ a : Γ(Y, LB.wchart L φ j),
      (π.app _).hom a = (res (le j) (u.s j)).val := fun j => (hπ _).2 _
  choose a ha using desc
  have hun : ∀ j, IsUnit (a j) := by
    intro j
    obtain ⟨b, hb⟩ := (hπ (LB.wchart L φ j)).2 ((res (le j) (u.s j))⁻¹).val
    refine IsUnit.of_mul_eq_one b ((hπ _).1 ?_)
    rw [map_mul, map_one, ha j, hb]
    exact Units.mul_inv _
  have hv : ∀ j (Z : Scheme.{0}) (r : Z ⟶ Y') (y : Z), π (r y) ∈ LB.wchart L φ j →
      gm (r ≫ π) y (LB.wchart L φ j) (hun j).unit =
      gm r y (LB.wchart L (fun k => π ≫ φ k) j) (u.s j) := by
    intro j Z r y hy
    have e : pullU π _ (hun j).unit = res (le j) (u.s j) := Units.ext (ha j)
    exact (gm_pull r π y _ hy _).symm.trans ((congrArg (gm r y _) e).trans (gm_res r y (le j) hy _))
  refine ⟨⟨fun j => (hun j).unit⟩, fun j j' => Units.ext
    ((hπ (LB.wchart L φ j ⊓ LB.wchart L φ j')).1 ?_), fun Z r z J hJ => ?_⟩
  · refine congrArg Units.val (unit_ext (a := pullU π _ _) (b := pullU π _ _) fun y hy => ?_)
    have hy' : π y ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := hy
    refine (gm_pull (𝟙 Y') π y _ hy' _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') π y _ hy' _).symm)
    refine ((gm_res (𝟙 Y' ≫ π) y _ hy' _).trans ((hv j _ _ y hy'.1).trans
      (gen_trans hu (𝟙 Y') y (le j hy'.1) (le j' hy'.2)))).trans (Eq.symm ?_)
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L φ ε (𝟙 Y' ≫ π) y j j' hy'.1 hy'.2).trans ?_)
      ((gm_res (𝟙 Y' ≫ π) y _ hy' _).trans (hv j' _ _ y hy'.2)))
    simp only [trF, Category.id_comp]
  · rw [val_of _ (r ≫ π) z J (fun k => J (r ≫ π ≫ φ k)) (fun k => by rw [Category.assoc])]
    exact hv _ Z r z (Set.mem_iInter.2 fun k => hJ (r ≫ π ≫ φ k))

theorem exists_descend_bij {M : LB X} {L : LB X'} {F : X' ⟶ X} {w : LB.Iso L (M.pull F)} (hw : PGen w)
    (hM : M.IsLB) (hL : L.IsLB) (π : Y' ⟶ Y) (hπ : ∀ V : Y.Opens, Function.Bijective (π.app V).hom)
    {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} (hc : ∀ k, φ' k ≫ F = π ≫ φ k) {ε : K → ℤ}
    (a : LB.Gen (LB.LinComb L φ' ε)) (ha : a.IsGen) :
    ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (I : (Z ⟶ X) → M.ι) (J : (Z ⟶ X') → L.ι), Good M z I → Good L z J →
        val t (r ≫ π) z I = (∏ k, gw w (r ≫ φ' k) z (I ((r ≫ φ' k) ≫ F)) (J (r ≫ φ' k)) ^ ε k) * val a r z J := by
  obtain ⟨t₁, ht₁, v₁⟩ := exists_up hw hM hL a ha
  obtain ⟨u, hu, vu⟩ := exists_gen hM (φ' := fun k => π ≫ φ k) (ε' := ε)
    (fun U _ h => Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ ε k) (hc k)) t₁ ht₁
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (I J), Good M z I → Good L z J → val u r z I =
      (∏ k, gw w (r ≫ φ' k) z (I ((r ≫ φ' k) ≫ F)) (J (r ≫ φ' k)) ^ ε k) * val a r z J := by
    intro Z r z I J hI hJ
    rw [vu Z r z I hI, val_of t₁ r z I (fun k => I ((r ≫ φ' k) ≫ F)) (fun k => by rw [Category.assoc])]
    exact v₁ Z r z _ _ (Set.mem_iInter.2 fun k => hI ((r ≫ φ' k) ≫ F)) (hJ.mem φ' r)
  obtain ⟨t, ht, vt⟩ := exists_gen_descend_val_bij π hπ φ ε u hu
  exact ⟨t, ht, fun Z r z I J hI hJ => (vt Z r z I hI).trans (key Z r z I J hI hJ)⟩

end GlobalTheory.Mum.BijDescent
