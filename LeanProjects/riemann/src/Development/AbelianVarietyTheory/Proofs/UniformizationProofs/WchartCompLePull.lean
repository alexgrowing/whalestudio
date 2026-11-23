import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LcgLinCombEqProd

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

lemma wchart_comp_le_pull {X X' Y : Scheme.{0}} (L : LB X) {J : Type} [Fintype J]
    (F : J → (X' ⟶ X)) (q : Y ⟶ X') (jN : J → L.ι) :
    LB.wchart L (fun i => q ≫ F i) jN ≤
      LB.wchart (LB.LinComb L F (fun _ => 1)) (fun _ : PUnit => q) (fun _ => jN) :=
  fun _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun i => Set.mem_iInter.1 hy i

noncomputable def genOfPullBox {X X' Y : Scheme.{0}} (L : LB X) {J : Type} [Fintype J]
    (F : J → (X' ⟶ X)) (q : Y ⟶ X') (a : LB.Gen ((LB.LinComb L F (fun _ => 1)).pull q)) :
    LB.Gen (LB.LinComb L (fun i => q ≫ F i) (fun _ => 1)) where
  s := fun jN => res (wchart_comp_le_pull L F q jN) (a.s (fun _ => jN))

theorem mapsAt_idIso {X X' Y : Scheme.{0}} (L : LB X) {J : Type} [Fintype J]
    (F : J → (X' ⟶ X)) (q : Y ⟶ X') (a : LB.Gen ((LB.LinComb L F (fun _ => 1)).pull q))
    (ha : a.IsGen) :
    GeneratorPullback.MapsAt L (LB.LinComb L F (fun _ => 1)) F (CubePf.idIsoL _) q 1 a (genOfPullBox L F q a) := by
  intro jN jL
  refine unit_ext fun y hy => ?_
  have h1 : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun i => q ≫ F i) jN :=
    GeneratorPullback.mapsAt_le_b L _ F q jN jL hy
  have h2 : (𝟙 Y : Y ⟶ Y) y ∈
      LB.wchart (LB.LinComb L F (fun _ => 1)) (fun _ : PUnit => q) (fun _ => jL) :=
    GeneratorPullback.mapsAt_le_a L _ F q jN jL hy
  have key := gen_trans ha (𝟙 Y) y (wchart_comp_le_pull L F q jN h1) h2
  refine ((gm_res _ y _ hy _).trans (gm_res _ y _ h1 _)).trans (key.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res _ y _ hy _))
  unfold trF
  rw [Fintype.prod_unique]
  exact (map_zpow _ _ _).trans (congrArg (· ^ (1 : ℤ)) (gm_pull (𝟙 Y) q y _ hy _))

theorem box_id_rig : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left), L.IsLB → ∀ r : LB.Gen (L.pull (eSec G)), r.IsGen → ∃ w : LB.Iso (boxLB L p.pr) (boxLB L p.pr), w.IsGen ∧ (∃ b : LB.Gen (LB.LinComb L (K := Fin j) (fun i => eSec G' ≫ (p.pr i).left) (fun _ => 1)), GeneratorPullback.MapsAt L (boxLB L p.pr) (fun i => (p.pr i).left) w (eSec G') 1 (boxRig p L r) b ∧ LB.Gen.Corr L _ _ _ _ b (GeneratorPullback.finProdGen L (J := Fin j) (fun _ _ => eSec G) (fun _ _ => 1) (fun _ => r))) ∧ ∀ (K : Type) [Fintype K] (Y : Scheme.{0}) (φ : K → (Y ⟶ G'.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb (boxLB L p.pr) φ ε)), t.IsGen → LB.Gen.Maps (LB.linCombIso w φ ε) t t := by
  intro S G' G _ _ _ _ j p L hL r hr
  refine ⟨CubePf.idIsoL _, CubePf.idIsoL_isGen (boxIsLB S G' G j p L hL),
    ⟨genOfPullBox L _ (eSec G') (boxRig p L r),
      mapsAt_idIso L _ _ _ (boxRigIsGen S G' G j p L r hL hr), ?_⟩,
    fun K _ Y φ ε t ht q => ht q.1 q.2⟩
  have he : ∀ i, eSec G' ≫ (p.pr i).left = eSec G := fun i => by
    letI := p.hom i
    exact (CubeMap.ofHom (p.pr i)).e_comm.trans (Category.id_comp _)
  intro a a' _ _ c
  refine unit_ext fun y hy => ?_
  have ha : ∀ i, a i = a' (i, PUnit.unit) := fun i => c i (i, PUnit.unit) (he i)
  refine ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.1 _)).trans
    (Eq.trans ?_ (gm_res _ y _ hy _).symm)
  refine (map_prod (gm (𝟙 _) y (LB.wchart (boxLB L p.pr) (fun _ : PUnit => eSec G') (fun _ => a)))
    _ (Finset.univ : Finset (Fin j))).trans (Eq.trans ?_ (map_prod (gm (𝟙 _) y
      (LB.wchart L (fun _ : Fin j × PUnit => eSec G) a')) _ (Finset.univ : Finset (Fin j))).symm)
  refine Finset.prod_congr rfl fun i _ => ?_
  have m1 := wchart_comp_le_pull L (fun i => (p.pr i).left) (eSec G') a hy.1
  have m2 := GeneratorPullback.box_le L (fun i => (p.pr i).left) (fun _ : PUnit => eSec G') (fun _ => a) i m1
  have m3 := rigPull_le (p.pr i).left (𝟙 _) ((he i).trans (Category.id_comp _).symm) L _ m2
  refine (gm_res _ y _ m1 _).trans ((gm_res _ y _ m2 _).trans
    ((gm_pull (𝟙 _) (𝟙 _) y _ m3 _).trans (Eq.trans ?_ (gm_res _ y _ hy.2 _).symm)))
  rw [Category.id_comp]
  have e : (fun _ : PUnit => a i) = fun k => a' (i, k) := funext fun _ => ha i
  exact congrArg (fun z => gm (𝟙 _) y (LB.wchart L (fun _ : PUnit => eSec G) z) (r.s z)) e

end GlobalTheory
