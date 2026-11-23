import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfAppLESectionEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGeometricallyIntegralAbLocusTensorObj
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory
namespace TripleMap

theorem exists_ratio {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {u u' : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L φ j →
      gm r z (LB.wchart L φ j) (u.s j) = gm r z ⊤ a * gm r z (LB.wchart L φ j) (u'.s j) := by
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι),
      gm r z (LB.wchart L φ j) (u.s j * (u'.s j)⁻¹) =
        gm r z (LB.wchart L φ j) (u.s j) * (gm r z (LB.wchart L φ j) (u'.s j))⁻¹ := fun Z r z j =>
    (map_mul _ _ _).trans (congrArg _ (map_inv _ _))
  obtain ⟨a, ha⟩ := glue_unit ⊤ (LB.wchart L φ) (fun _ => le_top)
    (fun y _ => by
      choose p hp using fun k => exists_chart hL (φ k y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp⟩) (fun j => u.s j * (u'.s j)⁻¹)
    (fun j j' y hy => by
      rw [hv, hv, gen_trans hu (𝟙 Y) y hy.1 hy.2, gen_trans hu' (𝟙 Y) y hy.1 hy.2, mul_inv,
        _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul])
  refine ⟨a, fun Z r z j hj => ?_⟩
  rw [← gm_res r z le_top hj a, ha j, hv, inv_mul_cancel_right]

theorem exists_rigidified {X X' S S' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB)
    (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : PGen w) (e : S ⟶ X) (e' : S' ⟶ X') (p : X' ⟶ S')
    (hp : e' ≫ p = 𝟙 _) (f : S' ⟶ S) (he : e' ≫ F = f ≫ e) (ρ : LB.Gen (L.pull e)) (hρ : ρ.IsGen)
    (ρ' : LB.Gen (L'.pull e')) (hρ' : ρ'.IsGen) :
    ∃ w' : LB.Iso L' (L.pull F), PGen w' ∧
      PMaps w' (K := PUnit) (fun _ => e') (fun _ => e) (fun _ => 1) ρ' ρ f := by
  obtain ⟨ρ₀, h₀, H⟩ := DegPull.exists_pmaps hw hL hL' (K := PUnit) (φ' := fun _ => e') (φ := fun _ => e)
    (ε := fun _ => 1) f (fun _ => he) ρ hρ
  obtain ⟨a, ha⟩ := exists_ratio hL' h₀ hρ'
  let w' : LB.Iso L' (L.pull F) := ⟨fun j => res le_top (pullU p ⊤ a) * w.s j⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι), F (r z) ∈ L.U j → r z ∈ L'.U k →
      gw w' r z j k = gm (r ≫ p) z ⊤ a * gw w r z j k := fun Z r z j k hj hk =>
    (map_mul _ _ _).trans (congrArg (· * _) ((gm_res r z _
      (show r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k from ⟨mem_pull.2 hj, hk⟩) _).trans
        (gm_pull r p z ⊤ trivial a)))
  refine ⟨w', fun Z r z j j' k k' hj hj' hk hk' => ?_, fun Z r z j k hj hk => ?_⟩
  · rw [key Z r z j k hj hk, key Z r z j' k' hj' hk', hw Z r z j j' k k' hj hj' hk hk', mul_left_comm]
  · rw [H Z r z j k hj hk, ha Z r z k (Set.mem_iInter.2 hk), Fintype.prod_unique, Fintype.prod_unique,
      key Z (r ≫ e') z _ _ (hj _) (hk _), Category.assoc, hp, Category.comp_id, zpow_one, zpow_one,
      ← _root_.mul_assoc, mul_comm (gm r z ⊤ a)]

theorem pmaps_cubical {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f F) {L : RigLB G}
    {L' : RigLB G'} (c : CubicalStr G L) (c' : CubicalStr G' L') {w : LB.Iso L'.L (L.L.pull F)} (hw : PGen w)
    (rigid : ∀ a : Γ((G3 G').left, ⊤)ˣ,
      (∀ y, gm (lift (1 : 𝟙_ (Over S') ⟶ G') (lift (1 : 𝟙_ (Over S') ⟶ G') (1 : 𝟙_ (Over S') ⟶ G'))).left y ⊤ a = 1) →
        a = 1) :
    PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε c'.t c.t (cubeMapOf gp).F3 := by
  have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ F = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  obtain ⟨t, ht, H⟩ := DegPull.exists_pmaps hw L.isLB L'.isLB (ε := thε) (cubeMapOf gp).F3 hψ c.t c.isGen
  obtain ⟨a, ha⟩ := exists_ratio L'.isLB ht c'.isGen
  have a1 : a = 1 := rigid a fun y => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' L.isLB y
    obtain ⟨J', hJ'⟩ := DegPull.exists_good' L'.isLB y
    let o : 𝟙_ (Over S') ⟶ G' := 1
    have e := DegPull.pmaps_val hψ H (lift o (lift o o)).left y hJ hJ'
    have q : (lift o (lift o o)).left ≫ (cubeMapOf gp).F3 =
        (lift (pushHom gp _ o) (lift (pushHom gp _ o) (pushHom gp _ o))).left := hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3] <;> rfl
    rw [q] at e
    have e₁ : cubV c y J (pushHom gp _ o) (pushHom gp _ o) (pushHom gp _ o) = 1 := by
      rw [map_one]
      exact (isCub_cubV c (T := Over.mk ((𝟙_ (Over S')).hom ≫ f)) hJ).face _ _
    have e₂ := prod_cub o o o (fun q => gw w q y (J (q ≫ F)) (J' q))
    have e₃ : cubV c' y J' o o o = 1 := (isCub_cubV c' hJ').face _ _
    have e₄ := ha _ (lift o (lift o o)).left y _ (hJ'.mem (thφ G' (x3 G')) _)
    have e₅ := e₁.symm.trans (e.trans (congrArg₂ (· * ·) e₂ (e₄.trans (congrArg _ e₃))))
    simp only [o, _root_.mul_one, mul_inv_cancel, inv_mul_cancel_right, mul_inv_cancel_right, _root_.one_mul, inv_mul_cancel] at e₅
    exact e₅.symm
  intro Z r z p q hp hq
  rw [H Z r z p q hp hq, ha Z r z q (Set.mem_iInter.2 hq), a1, map_one, _root_.one_mul]

end TripleMap

theorem exists_sabMap_of_lbIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (φ : t'.G.left ⟶ t.G.left), (IsReduced X' ∧ genericPoints X' ⊆ abLocus t'.G) → IsGrpPullback t'.G t.G f φ → (∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left) → LBIso t'.PP.L (t.PP.L.pull φ) → ∃ ν : SABMap t' t f, ν.φ = φ := by
  intro E _ _ _ H X X' t t' f φ ⟨hr, hab⟩ gp hact ⟨w, hw⟩
  obtain ⟨w', hw', Hr⟩ := TripleMap.exists_rigidified t.PP.isLB t'.PP.isLB w ((isGen_iff w).1 hw) (eSec t.G)
    (eSec t'.G) t'.G.hom (Over.w _) f (cubeMapOf gp).e_comm t.PP.rig t.PP.rigGen t'.PP.rig t'.PP.rigGen
  have sm := t'.semi.smooth
  have gc := t'.semi.geomConnected
  have gi := grpObj_geometricallyIntegral_of_smooth X' t'.G
  obtain ⟨s₂, i₂, l₂⟩ := smooth_geometricallyIntegral_abLocus_tensorObj X' t'.G t'.G sm sm gi gi
  obtain ⟨s₃, i₃, l₃⟩ := smooth_geometricallyIntegral_abLocus_tensorObj X' t'.G (t'.G ⊗ t'.G) sm s₂ gi i₂
  refine ⟨⟨cubeMapOf gp, gp, rfl, hact, (isPullCubical_iff _ _ _).2 ⟨w', hw', Hr,
    TripleMap.pmaps_cubical gp t.cub t'.cub hw' fun a ha => ?_⟩⟩, rfl⟩
  let o := lift (1 : 𝟙_ (Over X') ⟶ t'.G) (lift (1 : 𝟙_ (Over X') ⟶ t'.G) (1 : 𝟙_ (Over X') ⟶ t'.G))
  have h₁ : pullU o.left ⊤ a = 1 := unit_ext fun y _ =>
    (gm_pull (𝟙 _) o.left y ⊤ trivial a).trans ((congrArg (fun q => gm q y ⊤ a) (Category.id_comp _)).trans
      ((ha y).trans (map_one _).symm))
  refine Units.ext (eq_one_of_appLE_section_eq_one X' (G3 t'.G) o.left (Over.w o) s₃ i₃
    ⟨hr, fun x hx => l₃ ⟨hab hx, l₂ ⟨hab hx, hab hx⟩⟩⟩ ⊤ a.val le_rfl ?_)
  exact (congrArg (fun q => q.hom a.val) (o.left.appLE_eq_app (U := ⊤))).trans (congrArg Units.val h₁)

end GlobalTheory
