import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RigidifiedIsoRespectsCubeAndSymmetry
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisationsAgreeAtLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GmSqPullG

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqLevel

variable {X Y : Scheme.{0}} {K : Type} [Fintype K]

theorem sqGen_le (L₀ : LB X) (φ : K → (Y ⟶ X)) (j : K → Fin 1 → L₀.ι) :
    LB.wchart (sqLB L₀) φ j ≤ LB.wchart L₀ φ (fun k => j k 0) :=
  fun _ hy => Set.mem_iInter.2 fun k => mem_sq.1 (Set.mem_iInter.1 hy k)

def sqGen {L₀ : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L₀ φ ε)) :
    LB.Gen (LB.LinComb (sqLB L₀) φ ε) :=
  ⟨fun j => res (sqGen_le L₀ φ j) (t.s (fun k => j k 0)) ^ 2⟩

theorem gm_sqGen {Z : Scheme.{0}} {L₀ : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L₀ φ ε))
    (r : Z ⟶ Y) (z : Z) (j : K → Fin 1 → L₀.ι) (hj : r z ∈ LB.wchart (sqLB L₀) φ j) :
    gm r z _ ((sqGen t).s j) = gm r z _ (t.s (fun k => j k 0)) ^ 2 :=
  (map_pow _ _ _).trans (congrArg (· ^ 2) (gm_res r z _ hj _))

theorem sqGen_isGen {L₀ : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L₀ φ ε)} (ht : t.IsGen) :
    (sqGen t).IsGen := by
  intro j j'
  apply unit_ext
  intro x hx
  have hj := sqGen_le L₀ φ j hx.1
  have hj' := sqGen_le L₀ φ j' hx.2
  have hm : (𝟙 Y) x ∈ (LB.LinComb L₀ φ ε).U (fun k => j k 0) ⊓ (LB.LinComb L₀ φ ε).U (fun k => j' k 0) := ⟨hj, hj'⟩
  have e := congrArg (gm (𝟙 Y) x _) (ht (fun k => j k 0) (fun k => j' k 0))
  rw [gm_res (𝟙 Y) x _ hm, map_mul, gm_res (𝟙 Y) x _ hm] at e
  erw [gm_linComb L₀ φ ε (𝟙 Y) x _ _ hj hj'] at e
  rw [gm_res _ x _ hx, map_mul, gm_res _ x _ hx, gm_sqGen t (𝟙 Y) x j hx.1, gm_sqGen t (𝟙 Y) x j' hx.2]
  erw [gm_linComb (sqLB L₀) φ ε (𝟙 Y) x j j' hx.1 hx.2]
  rw [e, mul_pow]
  congr 1
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  have a₁ : (𝟙 Y ≫ φ k) x ∈ L₀.U (j k 0) := Set.mem_iInter.1 hj k
  have a₂ : (𝟙 Y ≫ φ k) x ∈ L₀.U (j' k 0) := Set.mem_iInter.1 hj' k
  rw [gm_sq_g L₀ (𝟙 Y ≫ φ k) x (j k) (j' k) a₁ a₂, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
    mul_comm]

theorem val_sqGen {Z : Scheme.{0}} {L₀ : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L₀ φ ε))
    {z : Z} {J : (Z ⟶ X) → Fin 1 → L₀.ι} (hJ : Good (sqLB L₀) z J) (r : Z ⟶ Y) :
    val (sqGen t) r z J = val t r z (fun ψ => J ψ 0) ^ 2 :=
  gm_sqGen t r z _ (hJ.mem φ r)

theorem good_sq {Z : Scheme.{0}} {L₀ : LB X} {z : Z} {J : (Z ⟶ X) → Fin 1 → L₀.ι} (hJ : Good (sqLB L₀) z J) :
    Good L₀ z (fun ψ => J ψ 0) :=
  fun ψ => mem_sq.1 (hJ ψ)

end GlobalTheory.SqLevel

namespace GlobalTheory

open RigidIsoCube SqLevel in

theorem sq_iso_carries_sq_cube : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (G3 G).left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t r z N ^ 2 =
        (∏ k : thK.{0}, gv wL (r ≫ thφ G (x3 G) k) z (fun _ => N (r ≫ thφ G (x3 G) k))
          (fun _ => N' (r ≫ thφ G (x3 G) k)) ^ thε k) *
        val (L := U'.LG.L) (φ := thφ G (x3 G)) (ε := thε) U'.cubG.t r z N' ^ 2 := by
  intro hG R _ _ _ I _ D D' A A' G _ _ _ U U' wL hw Z r z N N' hN hN'
  have := U.smooth
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hg : IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) A.A.hom G.hom (jK R) := by
    have : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
    have s : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK R)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w U.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))
  have s₁ : Function.Surjective G.hom.appTop.hom :=
    surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ A.isAb).2
  have : Flat (G ⊗ G).hom := by rw [Over.tensorObj_hom]; infer_instance
  have sj : Function.Surjective ((snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom).appTop.hom :=
    surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _)
      (surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _) s₁)
  have hL := DVR.linComb_isLB U.LG.L U.LG.isLB (fun _ : Fin 1 => 𝟙 G.left) (fun _ => 2)
  have hL' := DVR.linComb_isLB U'.LG.L U'.LG.isLB (fun _ : Fin 1 => 𝟙 G.left) (fun _ => 2)
  have pg : PGen (isoPullId wL (rfl : 𝟙 G.left = 𝟙 G.left)) := isoPullId_pgen hw rfl
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 G := lift 1 (lift 1 1)
  have he : e.left ≫ (snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have PM := pmaps_of_section pg hL hL' (φ' := thφ G (x3 G)) (φ := thφ G (x3 G)) (ε := thε)
    (sqGen U'.cubG.t) (sqGen_isGen U'.cubG.isGen) (sqGen U.cubG.t) (sqGen_isGen U.cubG.isGen)
    (fun _ => Category.comp_id _) _ e.left he sj fun y J J' hJ hJ' => by
      refine (val_sqGen _ hJ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_sqGen _ hJ' _)).symm)
      have c₁ : val U.cubG.t e.left y (fun ψ => J ψ 0) = 1 := (isCub_cubV U.cubG (good_sq hJ)).face 1 1
      have c₂ : val U'.cubG.t e.left y (fun ψ => J' ψ 0) = 1 := (isCub_cubV U'.cubG (good_sq hJ')).face 1 1
      have p := prod_cub (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G) 1 1
        (fun q => gw (isoPullId wL (rfl : 𝟙 G.left = 𝟙 G.left)) q y (J (q ≫ 𝟙 _)) (J' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine (congrArg (· ^ 2) c₁).trans (Eq.trans ?_ (congrArg₂ (· * ·) p (congrArg (· ^ 2) c₂)).symm)
      simp
  have hp : ∀ k, (r ≫ thφ G (x3 G) k) z ∈ (sqLB U.LG.L).U (fun _ => N (r ≫ thφ G (x3 G) k)) :=
    fun k => mem_sq.2 (hN _)
  have hq : ∀ k, (r ≫ thφ G (x3 G) k) z ∈ (sqLB U'.LG.L).U (fun _ => N' (r ≫ thφ G (x3 G) k)) :=
    fun k => mem_sq.2 (hN' _)
  have v := PM Z r z (fun k _ => N (r ≫ thφ G (x3 G) k)) (fun k _ => N' (r ≫ thφ G (x3 G) k)) hp hq
  rw [Category.comp_id] at v
  refine (gm_sqGen U.cubG.t r z (fun k _ => N (r ≫ thφ G (x3 G) k)) (Set.mem_iInter.2 hp)).symm.trans
    (v.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_)
      (gm_sqGen U'.cubG.t r z (fun k _ => N' (r ≫ thφ G (x3 G) k)) (Set.mem_iInter.2 hq))))
  exact congrArg (· ^ thε k) (gw_isoPullId wL rfl _ z _ _ (hp k) (hq k))

end GlobalTheory
