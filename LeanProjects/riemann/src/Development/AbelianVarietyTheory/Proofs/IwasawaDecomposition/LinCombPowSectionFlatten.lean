import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem linComb_pow_pow_sec {X Y : Scheme.{0}} (L : LB X) (a n m : ℤ) (hm : m = a * n) (g : Y ⟶ X)
    (s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g) (fun _ => n))) :
    ∃ s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι),
      g (r z) ∈ L.U j → gs r z _ (s'.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j) := by
  let M := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)
  let N := LB.LinComb M (K := Fin 1) (fun _ => g) (fun _ => n)
  let P := LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)
  have le : ∀ i : Fin 1 → L.ι, P.U i ≤ N.U (fun k _ => i k) := fun i y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy k
  have gN : ∀ (x : Y) (i j : Fin 1 → L.ι) (hi : x ∈ P.U i) (hj : x ∈ P.U j),
      gm (𝟙 Y) x (P.U i ⊓ P.U j) (P.g i j) =
        gm (𝟙 Y) x (N.U (fun k _ => i k) ⊓ N.U (fun k _ => j k)) (N.g (fun k _ => i k) (fun k _ => j k)) := by
    intro x i j hi hj
    refine (gm_linComb L (fun _ : Fin 1 => g) (fun _ => m) (𝟙 Y) x i j hi hj).trans
      (Eq.trans ?_ (gm_linComb M (fun _ : Fin 1 => g) (fun _ => n) (𝟙 Y) x _ _ (le i hi) (le j hj)).symm)
    simp only [Fintype.prod_unique]
    refine Eq.trans ?_ (congrArg (· ^ n) (gm_linComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => a) (𝟙 Y ≫ g) x
      (fun _ => i default) (fun _ => j default) (Set.mem_iInter.1 (le i hi) default)
      (Set.mem_iInter.1 (le j hj) default))).symm
    simp only [Fintype.prod_unique, Category.comp_id, hm, zpow_mul]
  refine ⟨⟨fun i => (Y.presheaf.map (homOfLE (le i)).op).hom (s.f (fun k _ => i k)), fun i j => ?_⟩, ?_⟩
  · apply fn_ext
    intro x hx
    have hx' : (𝟙 Y) x ∈ P.U i ⊓ P.U j := hx
    have hN : (𝟙 Y) x ∈ N.U (fun k _ => i k) ⊓ N.U (fun k _ => j k) := ⟨le i hx.1, le j hx.2⟩
    have e := congrArg (gs (𝟙 Y) x _) (s.compat (fun k _ => i k) (fun k _ => j k))
    rw [gs_res _ _ _ hN, gs_mul _ _ _ hN, gs_unit _ _ _ hN, gs_res _ _ _ hN] at e
    have hi : (𝟙 Y) x ∈ P.U i := hx.1
    have hj : (𝟙 Y) x ∈ P.U j := hx.2
    rw [gs_res _ _ _ hx', gs_res (𝟙 Y) x (le i) hi, gs_mul _ _ _ hx', gs_unit _ _ _ hx', gs_res _ _ _ hx',
      gs_res (𝟙 Y) x (le j) hj, e, gN x i j hx.1 hx.2]
  · intro Z r z j hj
    have hz : r z ∈ P.U (fun _ => j) := Set.mem_iInter.2 fun _ => hj
    exact gs_res r z (le _) hz _

end GlobalTheory
