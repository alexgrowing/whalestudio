import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSchemeCubicalBundleExistsAndMaps
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CartTriple

section Charts

variable {X Y : Scheme.{0}} {M : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem chart_of_val (hM : M.IsLB) {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (α : (Z.presheaf.stalk z)ˣ)
    (h : ∀ J, Good M z J → val u r z J = α * val u' r z J) (q : K → M.ι) (hq : r z ∈ LB.wchart M φ q) :
    gm r z (LB.wchart M φ q) (u.s q) = α * gm r z (LB.wchart M φ q) (u'.s q) := by
  obtain ⟨J, hJ⟩ := GlobalTheory.DegPull.exists_good' hM z
  rw [gen_trans hu r z hq (hJ.mem φ r), gen_trans hu' r z hq (hJ.mem φ r), mul_left_comm]
  exact congrArg _ (h J hJ)

end Charts

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'} [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {F : G'.left ⟶ G.left}

omit [IsCommMonObj G] [IsCommMonObj G'] in

theorem exists_rigidified (he : eSec G' ≫ F = f ≫ eSec G) (L : RigLB G) (L' : RigLB G')
    (h : LBIso L'.L (L.L.pull F)) : ∃ w : LB.Iso L'.L (L.L.pull F), PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig f := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨ρ, hρ, H⟩ := GlobalTheory.DegPull.exists_pmaps ((isGen_iff w).1 hw) L.isLB L'.isLB (K := PUnit)
    (φ' := fun _ => eSec G') (φ := fun _ => eSec G) (ε := fun _ => 1) f (fun _ => he) L.rig L.rigGen
  obtain ⟨a, ha⟩ := GlobalTheory.AbPackage.exists_unit_ratio L'.isLB (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1)
    hρ L'.rigGen
  let b : Γ(G'.left, ⊤)ˣ := pullU G'.hom ⊤ a
  refine ⟨GlobalTheory.UU.scaleGen b w, (isGen_iff _).1 (GlobalTheory.UU.scaleGen_isGen b hw), fun Z r z p q hp hq => ?_⟩
  have hs : eSec G' ≫ G'.hom = 𝟙 _ := Over.w η[G']
  have e : gw (GlobalTheory.UU.scaleGen b w) (r ≫ eSec G') z (p PUnit.unit) (q PUnit.unit) =
      gm r z ⊤ a * gw w (r ≫ eSec G') z (p PUnit.unit) (q PUnit.unit) := by
    have hm : (r ≫ eSec G') z ∈ (L.L.pull F).U (fun _ => p PUnit.unit) ⊓ L'.L.U (q PUnit.unit) :=
      ⟨mem_pull.2 (hp PUnit.unit), hq PUnit.unit⟩
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ z le_top hm b).trans
      ((gm_pull (r ≫ eSec G') G'.hom z ⊤ trivial a).trans ?_)) rfl)
    rw [Category.assoc, hs]
    exact congrArg (fun g => gm g z ⊤ a) (Category.comp_id r)
  have e₂ := chart_of_val L'.isLB (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1) hρ L'.rigGen r z _
    (ha Z r z) q (Set.mem_iInter.2 hq)
  refine (H Z r z p q hp hq).trans ((congrArg (_ * ·) e₂).trans ?_)
  rw [Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one, ← _root_.mul_assoc]
  exact congrArg (· * _) ((mul_comm _ _).trans e.symm)

theorem val_origin (gp : IsGrpPullback G' G f F) {L : RigLB G} {L' : RigLB G'} (c : CubicalStr G L)
    {w : LB.Iso L'.L (L.L.pull F)} {t : LB.Gen (LB.LinComb L'.L (thφ G' (x3 G')) thε)}
    (H : PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε t c.t (cubeMapOf gp).F3) (T : Over S') (y : T.left) (J')
    (hJ' : Good L'.L y J') : val t (lift (1 : T ⟶ G') (lift 1 1)).left y J' = 1 := by
  have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ F = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  obtain ⟨J, hJ⟩ := GlobalTheory.DegPull.exists_good' L.isLB y
  have q : ∀ a : T ⟶ G', (lift a (lift a a)).left ≫ (cubeMapOf gp).F3 =
      (lift (pushHom gp T a) (lift (pushHom gp T a) (pushHom gp T a))).left := fun a => hom_ext_triple _ fun i => by
    rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i <;> simp [x3] <;> rfl
  have e := GlobalTheory.DegPull.pmaps_val hψ H (lift (1 : T ⟶ G') (lift 1 1)).left y hJ hJ'
  rw [q, map_one] at e
  have p := prod_cub (1 : T ⟶ G') 1 1 (fun q => gw w q y (J (q ≫ F)) (J' q))
  rw [_root_.mul_one, _root_.mul_one] at p
  have e' := ((isCub_cubV c (T := Over.mk (T.hom ≫ f)) hJ).face 1 1).symm.trans
    (e.trans (congrArg₂ (· * ·) p rfl))
  have alg : ∀ {U : Type} [CommGroup U] (a v : U), 1 = a * a⁻¹ * a⁻¹ * a⁻¹ * a * a * a * a⁻¹ * v → v = 1 :=
    fun a v h => by simpa using h.symm
  exact alg _ _ e'

theorem pmaps_cube (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme G') (gp : IsGrpPullback G' G f F) {L : RigLB G}
    {L' : RigLB G'} (c : CubicalStr G L) (c' : CubicalStr G' L') {w : LB.Iso L'.L (L.L.pull F)} (hw : PGen w) :
    PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε c'.t c.t (cubeMapOf gp).F3 := by
  have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ F = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  obtain ⟨t, ht, H⟩ := GlobalTheory.DegPull.exists_pmaps hw L.isLB L'.isLB (ε := thε) (cubeMapOf gp).F3 hψ c.t c.isGen
  have key := gen_unique L'.isLB (φ := thφ G' (x3 G')) (ε := thε) (G3 G').hom
    (lift (1 : 𝟙_ (Over S') ⟶ G') (lift 1 1)).left (Over.w _) (GlobalTheory.UU.surjective_cube hG hA) ht c'.isGen
    (fun y J' hJ' => (val_origin gp c H (𝟙_ (Over S')) y J' hJ').trans ((isCub_cubV c' hJ').face 1 1).symm)
  intro Z r z p q hp hq
  have e := (chart_of_val L'.isLB (φ := thφ G' (x3 G')) (ε := thε) ht c'.isGen r z 1
    (fun J hJ => (key Z r z J hJ).trans (_root_.one_mul _).symm) q (Set.mem_iInter.2 hq)).trans (_root_.one_mul _)
  exact (H Z r z p q hp hq).trans (congrArg₂ (· * ·) rfl e)

theorem isPullCubical_of_iso (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme G') (gp : IsGrpPullback G' G f F)
    {L : RigLB G} {L' : RigLB G'} (c : CubicalStr G L) (c' : CubicalStr G' L') (h : LBIso L'.L (L.L.pull F)) :
    (cubeMapOf gp).IsPullCubical c' c := by
  obtain ⟨w, hw, hr⟩ := exists_rigidified (cubeMapOf gp).e_comm L L' h
  exact (isPullCubical_iff _ c c').2 ⟨w, hw, hr, pmaps_cube hG hA gp c c' hw⟩

theorem exists_tripleMap : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (t : SAB H S) (φ : t'.G.left ⟶ t.G.left), IsAbelianScheme t'.G → IsGrpPullback t'.G t.G f φ → (∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left) → LBIso t'.PP.L (t.PP.L.pull φ) → ∃ m : SABMap t' t f, m.φ = φ := by
  intro hG E _ _ _ H S S' f t' t φ hA gp hact h
  exact ⟨⟨cubeMapOf gp, gp, rfl, hact, isPullCubical_of_iso hG hA gp t.cub t'.cub h⟩, rfl⟩

end GlobalTheory.CartTriple
