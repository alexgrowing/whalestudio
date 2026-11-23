import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumOf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch.FibCube
open GlobalTheory.FrameValue GlobalTheory.TorusExt

theorem vF_eq_genVal_mul {X Y Y' : Scheme.{0}} {L : LB X} {A : Over (Sp ℂ)} [GrpObj A] {L' : LB A.left} {g : ℕ}
    (u : HolUnif A L' g) (hL' : L'.IsLB) {Φ : A.left ⟶ X} {w : LB.Iso L' (L.pull Φ)} {K : Type} [Fintype K]
    {φ' : K → (Y' ⟶ A.left)} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y} (hψ : ∀ k, φ' k ≫ Φ = h ≫ φ k)
    {a : LB.Gen (LB.LinComb L' φ' ε)} (ha : a.IsGen) {t : LB.Gen (LB.LinComb L φ ε)} (H : PMaps w φ' φ ε a t h)
    {J : (Sp ℂ ⟶ X) → L.ι} (hJ : ∀ ψ : Sp ℂ ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) (fr : (Fin g → ℂ) → ℂˣ)
    (hfr : ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U i →
      (fr z : ℂ) = valAt' (u.ex z).left _ (w.s (fun _ => J ((u.ex z).left ≫ Φ), i)).val * u.fr i z)
    {r : Sp ℂ ⟶ Y'} {z : K → Fin g → ℂ} (hz : IsLift u φ' r z) :
    vF t (r ≫ h) J = genVal u hL' a r z * ((∏ k, fr (z k) ^ ε k : ℂˣ) : ℂ) := by
  let p : Sp ℂ := (default : PrimeSpectrum ℂ)
  let J' : (Sp ℂ ⟶ A.left) → L'.ι := chartAt hL'
  have hJ' : ∀ ψ : Sp ℂ ⟶ A.left, ⊤ ≤ ψ ⁻¹ᵁ L'.U (J' ψ) := le_chartAt hL'
  have e := congrArg (fun q => (((stalkUnits p).symm q : ℂˣ) : ℂ))
    (DegPull.pmaps_val hψ H r p (J := J) (J' := J') (fun ψ => hJ ψ trivial) (fun ψ => hJ' ψ trivial))
  have e₁ : vF a r J' = genVal u hL' a r z * frameProd u ε z (fun k => J' (r ≫ φ' k)) :=
    valAt'_gen hL' ha hz (le_wchart_chartAt hL' φ' r)
  have e₂ : ∀ v, (((stalkUnits p).symm (gw w (u.ex v).left p (J ((u.ex v).left ≫ Φ)) (J' (u.ex v).left)) : ℂˣ) : ℂ) *
      u.fr (J' (u.ex v).left) v = fr v := fun v => by
    rw [hfr v _ (hJ' _)]
    refine congrArg (· * _) ((stalkConst p).injective ?_)
    have m : ⊤ ≤ (u.ex v).left ⁻¹ᵁ ((L.pull Φ).U (fun _ => J ((u.ex v).left ≫ Φ)) ⊓ L'.U (J' (u.ex v).left)) :=
      fun y hy => ⟨mem_pull.2 (hJ ((u.ex v).left ≫ Φ) hy), hJ' _ hy⟩
    rw [← stalkUnits_val, MulEquiv.apply_symm_apply]
    exact (gs_unit (u.ex v).left p ((L.pull Φ).U (fun _ => J ((u.ex v).left ≫ Φ)) ⊓ L'.U (J' (u.ex v).left))
      (m trivial) _).symm.trans (gs_eq_stalkConst _ p m _)
  simp only [map_mul, map_prod, map_zpow, Units.val_mul] at e
  rw [GaugeValues.vF_eq hJ, GaugeValues.vF_eq hJ', e₁] at e
  rw [e, mul_left_comm]
  congr 1
  rw [frameProd, Units.coe_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, ← mul_zpow, hz k, e₂]

theorem exists_cube_down {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'} [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f F) {L : RigLB G}
    (c : CubicalStr G L) {L' : LB G'.left} (hL' : L'.IsLB) {w : LB.Iso L' (L.L.pull F)} (hw : w.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' (thφ G' (x3 G')) thε), a.IsGen ∧
      PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε a c.t (cubeMapOf gp).F3 ∧
      LB.Gen.Corr L' _ _ (Y := (G2 G').left) _ _ (LB.pullGen L' (thφ G' (x3 G')) thε a (faceMap G' 0).left)
        (LB.oneGen L') := by
  have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ F = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  obtain ⟨a, ha, H⟩ := DegPull.exists_pmaps ((isGen_iff w).1 hw) L.isLB hL' (ε := thε) (cubeMapOf gp).F3 hψ c.t c.isGen
  refine ⟨a, ha, H, corr_of_val hL' fun y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := DegPull.exists_good' L.isLB y
  have e := DegPull.pmaps_val hψ H (lift (1 : G2 G' ⟶ G') (lift (x2 G' 0) (x2 G' 1))).left y hJ hJ'
  have q : ∀ a b c : G2 G' ⟶ G', (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 =
      (lift (pushHom gp _ a) (lift (pushHom gp _ b) (pushHom gp _ c))).left := fun a b c =>
    hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3] <;> rfl
  rw [q, map_one] at e
  have p := prod_cub (1 : G2 G' ⟶ G') (x2 G' 0) (x2 G' 1) (fun q => gw w q y (J (q ≫ F)) (J' q))
  rw [_root_.one_mul, _root_.one_mul] at p
  have e' := ((isCub_cubV c (T := Over.mk ((G2 G').hom ≫ f)) hJ).face _ _).symm.trans (e.trans (congrArg (· * _) p))
  refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ (val_one _).symm)
  rw [Category.id_comp]
  apply Additive.ofMul.injective
  have e'' := congrArg Additive.ofMul e'
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e'' ⊢
  refine Eq.trans ?_ e''.symm
  abel

end GlobalTheory.Ex.Arch.FibCube

namespace GlobalTheory.Ex.Arch
open GlobalTheory.FrameValue GlobalTheory.CubeValues

theorem fibCubeSt : Laws → FibCubeSt := by
  rintro - R _ _ _ D J g Λ Hm χ ex fr ⟨hJ, P', φ, w, u, hΛ, gp, hw, hAH, -, -, -, hex, hfr⟩ x y z
  obtain ⟨a, ha, H, hf⟩ := FibCube.exists_cube_down gp D.cub P'.isLB hw
  have e := FibCube.vF_eq_genVal_mul (L := D.P.L) (Φ := φ) (w := w) u P'.isLB (fun I : thK => (cubeMapOf gp).psum_comm I.down) ha H hJ fr
    (fun v i hi => by rw [← hex v]; exact hfr v i hi) (isLift_cube u ![x, y, z])
  replace e := e.trans ((congrArg (· * _) (genVal_cube_of_face P'.isLB hAH a ha hf _)).trans (_root_.one_mul _))
  have q : (pt3 u ![x, y, z]).left ≫ (cubeMapOf gp).F3 = (lift (ex x) (lift (ex y) (ex z))).left :=
    hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3, pt3, hex] <;> rfl
  have p := prod_thK fun I => fr (∑ a ∈ I, ![x, y, z] a)
  simp only [sum_three, Finset.sum_singleton, Finset.sum_empty, Matrix.cons_val] at p
  rw [q] at e
  refine (congrArg (fun s : ℂ => s * fr (x + y) * fr (x + z) * fr (y + z) * fr 0)
    (e.trans (congrArg Units.val p))).trans ?_
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

end GlobalTheory.Ex.Arch
end
