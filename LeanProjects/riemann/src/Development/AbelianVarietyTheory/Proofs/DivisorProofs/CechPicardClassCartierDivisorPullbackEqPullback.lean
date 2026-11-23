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
open GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory.PullCartier

theorem fnOf_app {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f]
    {U : W.Opens} (h : genericPoint M ∈ f ⁻¹ᵁ U) (a : Γ(W, U)) :
    fnOf (f ⁻¹ᵁ U) h ((f.app U).hom a) =
      GlobalTheory.functionFieldMap f (fnOf U (gen_mem (x := f (genericPoint M)) h) a) := by
  have hx : f (genericPoint M) ∈ U := h
  rw [← algebraMap_germ hx a, GlobalTheory.functionFieldMap_algebraMap, Scheme.Hom.germ_stalkMap_apply f U _ hx a]
  exact (algebraMap_germ (X := M) (U := f ⁻¹ᵁ U) (x := genericPoint M) h _).symm

theorem cls_toLB_pull : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f]
    (D₀ : CartierDiv W) (D₁ : CartierDiv M),
    (∀ x g, D₀.IsEqn (f x) g → D₁.IsEqn x (Units.map (GlobalTheory.functionFieldMap f).toMonoidHom g)) →
      cls (toLB D₁) (isLB_toLB D₁) = CechPic.pull f (cls (toLB D₀) (isLB_toLB D₀)) := by
  intro M W _ _ f _ D₀ D₁ hD
  have hP : Presents D₁ ((toLB D₀).pull f)
      fun J => Units.map (GlobalTheory.functionFieldMap f).toMonoidHom (J PUnit.unit).1.2 := by
    refine ⟨pull_isLB (isLB_toLB D₀) f, fun J K h => ?_,
      fun J x hx => hD x _ ((J PUnit.unit).2.2 _ (mem_pull.1 hx))⟩
    have hle : ((toLB D₀).pull f).U J ⊓ ((toLB D₀).pull f).U K ≤
        f ⁻¹ᵁ ((toLB D₀).U (J PUnit.unit) ⊓ (toLB D₀).U (K PUnit.unit)) :=
      fun y hy => ⟨mem_pull.1 hy.1, mem_pull.1 hy.2⟩
    have e0 : ((toLB D₀).pull f).g J K =
        res hle (pullU f _ ((toLB D₀).g (J PUnit.unit) (K PUnit.unit))) :=
      by dsimp only [LB.pull, LB.LinComb]; rw [Fintype.prod_unique, zpow_one]; rfl
    have e : fnOf _ h (((toLB D₀).pull f).g J K).val =
        fnOf _ (hle h) ((f.app _).hom ((toLB D₀).g (J PUnit.unit) (K PUnit.unit)).val) := by
      rw [e0, LB.val_res, fnOf_resG]
      rfl
    rw [e, fnOf_app, fnOf_toLB_g]
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    rw [← map_mul, div_mul_cancel₀ _ (Units.ne_zero _)]
  rw [← cls_pull (isLB_toLB D₀) f hP.isLB, ← toPic_apply, hP.toPic_eq]

end GlobalTheory.PullCartier
