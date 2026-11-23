import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.PullPres

theorem fnOf_app {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W] (q : X ⟶ W) [IsDominant q]
    {U : W.Opens} (h : genericPoint X ∈ q ⁻¹ᵁ U) (a : Γ(W, U)) :
    fnOf (q ⁻¹ᵁ U) h ((q.app U).hom a) =
      functionFieldMap q (fnOf U (gen_mem (x := q (genericPoint X)) h) a) := by
  rw [← algebraMap_germ h, ← algebraMap_germ (show q (genericPoint X) ∈ U from h),
    functionFieldMap_algebraMap, Scheme.Hom.germ_stalkMap_apply]

theorem fnOf_res_pullU {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W] (q : X ⟶ W) [IsDominant q]
    {U : W.Opens} {V : X.Opens} (le : V ≤ q ⁻¹ᵁ U) (hV : genericPoint X ∈ V) (u : Γ(W, U)ˣ) :
    fnOf V hV (res le (pullU q U u)).val =
      functionFieldMap q (fnOf U (gen_mem (x := q (genericPoint X)) (le hV)) u.val) :=
  (fnOf_resG le hV _).trans (fnOf_app q (le hV) _)

theorem presents_pull {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W] (q : X ⟶ W) [IsDominant q]
    (D : CartierDiv X) (E : CartierDiv W)
    (hDE : ∀ y b, E.IsEqn y b → ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b)) :
    Presents D ((toLB E).pull q) fun J => Units.map (functionFieldMap q).toMonoidHom (J PUnit.unit).1.2 := by
  refine ⟨pull_isLB (isLB_toLB E) q, fun J K h => ?_, fun J x hx => hDE _ _ ((J PUnit.unit).2.2 _ (mem_pull.1 hx)) x rfl⟩
  have le : ((toLB E).pull q).U J ⊓ ((toLB E).pull q).U K ≤
      q ⁻¹ᵁ ((toLB E).U (J PUnit.unit) ⊓ (toLB E).U (K PUnit.unit)) :=
    fun y hy => ⟨mem_pull.1 hy.1, mem_pull.1 hy.2⟩
  have hg : ((toLB E).pull q).g J K = res le (pullU q _ ((toLB E).g (J PUnit.unit) (K PUnit.unit))) := by
    simp only [LB.pull, LB.LinComb, Fintype.prod_unique, zpow_one]
    rfl
  rw [hg, fnOf_res_pullU, fnOf_toLB_g]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_div₀]
  exact (div_mul_cancel₀ _ ((map_ne_zero _).2 (Units.ne_zero _))).symm

theorem pull_cls_toLB : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (q : X ⟶ W) [IsDominant q]
    (D : CartierDiv X) (E : CartierDiv W),
    (∀ y b, E.IsEqn y b → ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b)) →
    CechPic.pull q (cls (toLB E) (isLB_toLB E)) = cls (toLB D) (isLB_toLB D) := by
  intro X W _ _ q _ D E hDE
  rw [← cls_pull (isLB_toLB E) q (pull_isLB (isLB_toLB E) q), ← (presents_pull q D E hDE).toPic_eq,
    toPic_apply]

end GlobalTheory.Cartier.PullPres
