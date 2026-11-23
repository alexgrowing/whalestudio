import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueCharacterOfMul

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.BiTrivUniq

variable {X Y : Scheme.{0}} {M : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem exists_unit_ratio (hM : M.IsLB) {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      val u r z J = gm r z ⊤ a * val u' r z J := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  rw [← mul_inv_eq_iff_eq_mul, ← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (gm_res r z le trivial _).symm

theorem gen_eq_of_val (hM : M.IsLB) {t t' : LB.Gen (LB.LinComb M φ ε)} (ht : t.IsGen) (ht' : t'.IsGen)
    (h : ∀ y J, Good M y J → val t (𝟙 Y) y J = val t' (𝟙 Y) y J) : t = t' := by
  obtain ⟨s⟩ := t
  obtain ⟨s'⟩ := t'
  congr 1
  funext j
  refine unit_ext (V := LB.wchart M φ j) fun y hy => ?_
  obtain ⟨I, hI⟩ := exists_good_pt hM y
  exact (gen_trans ht (𝟙 Y) y hy (Good.mem hI φ (𝟙 Y))).trans ((congrArg _ (h y I hI)).trans
    (gen_trans ht' (𝟙 Y) y hy (Good.mem hI φ (𝟙 Y))).symm)

end GlobalTheory.UU.BiTrivUniq

namespace GlobalTheory.UU
open BiTrivUniq

theorem biTriv_unique : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    [ConnectedSpace G.left] (L : RigLB G) (c : CubicalStr G L) (i : splitTorus S X ⟶ G), IsMonHom i →
    ∀ s s' : BiTriv c i, s = s' := by
  intro S X _ G _ _ _ L c i _ s s'
  obtain ⟨ρ, hρ⟩ := exists_unit_ratio L.isLB s.gen s'.gen
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.existsUnique_character_of_mul S X G ρ fun Z t t' y => by
    have e : Units.map (lift (t * t') y).left.appTop.hom.toMonoidHom ρ =
        Units.map (lift t y).left.appTop.hom.toMonoidHom ρ * Units.map (lift t' y).left.appTop.hom.toMonoidHom ρ := by
      refine unit_ext fun z _ => ?_
      obtain ⟨J, hJ⟩ := exists_good_pt L.isLB z
      have a := s.law1 Z t t' y z J hJ
      rw [hρ _ _ z J hJ, hρ _ _ z J hJ, hρ _ _ z J hJ, s'.law1 Z t t' y z J hJ] at a
      rw [map_mul, ← gm_top, ← gm_top, ← gm_top]
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul a
      simp only [ofMul_mul] at a' ⊢
      linear_combination (norm := abel) a'
    exact congrArg Units.val e
  have key : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (x : Z ⟶ G) (z : Z.left),
      gm (lift t x).left z ⊤ ρ = gm (𝟙 Z.left) z ⊤ (chV t χ) := fun Z t x z => by
    rw [gm_top]
    congr 1
    refine Units.ext ?_
    rw [chV_val]
    show (lift t x).left.appTop.hom ρ.val = _
    rw [hχ, Rosenlicht.over_appTop_comp, lift_fst]
  have hs : s.s = s'.s := gen_eq_of_val L.isLB s.gen s'.gen fun y J hJ => by
    have a := hρ _ (lift (fst (splitTorus S X) G) (1 : _ ⟶ G)).left y J hJ
    rw [s.val_one_right hJ, s'.val_one_right hJ, key, _root_.mul_one, ← key _ _ (snd _ _), lift_fst_snd,
      Over.id_left] at a
    rw [hρ _ _ y J hJ, ← a, _root_.one_mul]
  obtain ⟨s, _, _, _⟩ := s
  obtain ⟨s', _, _, _⟩ := s'
  obtain rfl : s = s' := hs
  rfl

end GlobalTheory.UU
end
