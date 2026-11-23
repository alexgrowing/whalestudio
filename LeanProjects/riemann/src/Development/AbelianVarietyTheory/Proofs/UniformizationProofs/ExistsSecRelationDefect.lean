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

namespace GlobalTheory

theorem exists_sec_smul_sub_smul {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s t : LB.Sec (LB.LinComb L φ ε)) (c' c : Γ(Y, ⊤)) : ∃ d : LB.Sec (LB.LinComb L φ ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
        sval d r z J = gs r z ⊤ c' * sval s r z J - gs r z ⊤ c * sval t r z J := by
  have gsub : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (_ : r z ∈ U) (a b : Γ(Y, U)),
      gs r z U (a - b) = gs r z U a - gs r z U b := fun Z r z U h a b => by
    simp only [gs_eq r z U h, map_sub]
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L φ j →
      gs r z (LB.wchart L φ j)
        ((Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c' * (show Γ(Y, LB.wchart L φ j) from s.f j) -
          (Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c * (show Γ(Y, LB.wchart L φ j) from t.f j)) =
      gs r z ⊤ c' * gs r z (LB.wchart L φ j) (s.f j) - gs r z ⊤ c * gs r z (LB.wchart L φ j) (t.f j) :=
    fun Z r z j hj => (gsub Z r z _ hj _ _).trans (congrArg₂ (· - ·)
      ((gs_mul r z _ hj _ _).trans (congrArg (· * _) (gs_res r z _ hj _)))
      ((gs_mul r z _ hj _ _).trans (congrArg (· * _) (gs_res r z _ hj _))))
  refine ⟨⟨fun j => (Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c' * (show Γ(Y, LB.wchart L φ j) from s.f j) -
          (Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c * (show Γ(Y, LB.wchart L φ j) from t.f j),
      fun (j j' : K → L.ι) => fn_ext fun y hy => ?_⟩, fun Z r z J hJ => v Z r z _ (hJ.mem φ r)⟩
  refine ((gs_res (𝟙 Y) y _ hy _).trans (v _ _ y j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
      (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2)))
      ((gs_res (𝟙 Y) y _ hy _).trans (v _ _ y j' hy.2)))).symm)
  rw [sec_trans s (𝟙 Y) y hy.1 hy.2, sec_trans t (𝟙 Y) y hy.1 hy.2]
  simp only [trF]
  ring

theorem exists_sec_relation_defect : ∀ (Y : Scheme.{0}) (X Y₂ : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K K' K'' : Type) [Fintype K] [Fintype K'] [Fintype K''] (φ : K → (Y₂ ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (φu : K'' → (Y ⟶ X)) (εu : K'' → ℤ) (τ : Y ⟶ Y₂) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (u : LB.Gen (LB.LinComb L φu εu)) (c c' : Γ(Y, ⊤)), u.IsGen → FormEq φ' ε' (Sum.elim (fun k => τ ≫ φ k) φu) (Sum.elim ε εu) → ∃ d : LB.Sec (LB.LinComb L φ' ε'), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval d r z J = gs r z ⊤ c' * sval s' r z J - gs r z ⊤ c * (sval s (r ≫ τ) z J * (val u r z J).val) := by
  intro Y X Y₂ L hL K K' K'' _ _ _ φ ε φ' ε' φu εu τ s s' u c c' hu hF
  obtain ⟨t, ht⟩ := exists_sec hL (fun U _ h => (hF U h).symm : FormEq _ _ φ' ε') (pullMulSec s τ u hu)
  obtain ⟨d, hd⟩ := exists_sec_smul_sub_smul s' t c' c
  exact ⟨d, fun Z r z J hJ => by rw [hd Z r z J hJ, ht Z r z J hJ, sval_pullMulSec s τ u hu r z hJ]⟩

end GlobalTheory
