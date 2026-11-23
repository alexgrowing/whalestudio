import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

theorem UpperTheory.pull_class_rational_power :
    ∀ (X Z : Scheme.{0}) [IsIntegral X] [IsIntegral Z] (g : X ⟶ Z) (hg : g (genericPoint X) ⤳ genericPoint Z) (L : LB X) (hL : L.IsLB) (s : L.ι → X.functionFieldˣ) (N : LB Z) (hN : N.IsLB) (s' : N.ι → Z.functionFieldˣ) (m : ℕ), IsRatSec L s → IsRatSec N s' → (∀ (x : X) (i : L.ι) (i' : N.ι), x ∈ L.U i → g x ∈ N.U i' → UnitAt x ((s i : X.functionField) ^ m / SmallSec.fnMap g hg (s' i' : Z.functionField))) → cls (N.pull g) (LB.isLB_pull hN g) = m • cls L hL := by
  intro X Z _ _ g hg L hL s N hN s' m hs hs' hu
  have hP := presents_divOfRatSec hL hs
  have hQ : Presents (m • divOfRatSec hL hs) (N.pull g)
      fun J => Units.map (SmallSec.fnMap g hg).toMonoidHom (s' (J PUnit.unit)) := by
    refine ⟨LB.isLB_pull hN g, fun J K h => ?_, fun J x hx => ?_⟩
    · have le : (N.pull g).U J ⊓ (N.pull g).U K ≤ g ⁻¹ᵁ (N.U (J PUnit.unit) ⊓ N.U (K PUnit.unit)) :=
        fun y hy => ⟨mem_pull.1 hy.1, mem_pull.1 hy.2⟩
      have hgg : (N.pull g).g J K = res le (pullU g _ (N.g (J PUnit.unit) (K PUnit.unit))) := by
        simp only [LB.pull, LB.LinComb, Fintype.prod_unique, zpow_one]
        rfl
      have hZ : genericPoint Z ∈ N.U (J PUnit.unit) ⊓ N.U (K PUnit.unit) :=
        gen_mem (x := g (genericPoint X)) (le h)
      have e : fnOf _ h (res le (pullU g _ (N.g (J PUnit.unit) (K PUnit.unit)))).val =
          SmallSec.fnMap g hg (fnOf _ hZ (N.g (J PUnit.unit) (K PUnit.unit)).val) :=
        (fnOf_resG le h _).trans (SmallSec.fnMap_fnOf g hg hZ (le h) _).symm
      rw [hgg, e]
      simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
      rw [hs' _ _ hZ, map_mul]
    · obtain ⟨i, hi⟩ := exists_chart hL x
      refine ((hP.isEqn i x hi).nsmul m).iff_unitAt.2 ?_
      have := (hu x i (J PUnit.unit) hi (mem_pull.1 hx)).inv
      rw [inv_div] at this
      simpa only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
        Units.val_pow_eq_pow_val] using this
  exact hQ.toPic_eq.symm.trans ((map_nsmul toPic m _).trans (congrArg (m • ·) hP.toPic_eq))
