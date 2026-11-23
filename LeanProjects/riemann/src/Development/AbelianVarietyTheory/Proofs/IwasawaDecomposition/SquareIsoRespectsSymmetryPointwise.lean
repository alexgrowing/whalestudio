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

namespace GlobalTheory.SqSym

open GlobalTheory.SqLevel

variable {X Y Z : Scheme.{0}} {K : Type} [Fintype K]

theorem sq_chart_le (L : LB X) (φ : K → (Y ⟶ X)) (j : K → Fin 1 → L.ι) :
    LB.wchart (sqLB L) φ j ≤ LB.wchart L φ (fun k => j k 0) :=
  fun _ hy => Set.mem_iInter.2 fun k => mem_sq.1 (Set.mem_iInter.1 hy k)

def sqGen (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) :
    LB.Gen (LB.LinComb (sqLB L) φ ε) :=
  ⟨fun j => res (sq_chart_le L φ j) (t.s (fun k => j k 0)) ^ 2⟩

theorem gm_sqGen {L : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    (j : K → Fin 1 → L.ι) (h : r z ∈ LB.wchart (sqLB L) φ j) :
    gm r z _ ((sqGen L φ ε t).s j) = gm r z _ (t.s (fun k => j k 0)) ^ 2 := by
  exact (map_pow _ _ _).trans (congrArg (· ^ 2) (gm_res r z _ h _))

theorem sqGen_isGen {L : LB X} (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    (ht : t.IsGen) : (sqGen L φ ε t).IsGen := by
  intro (i : K → Fin 1 → L.ι) (j : K → Fin 1 → L.ι)
  apply unit_ext
  intro y hy
  have hi := sq_chart_le L φ i hy.1
  have hj := sq_chart_le L φ j hy.2
  rw [gm_res (𝟙 _) y _ hy, map_mul, gm_res (𝟙 _) y _ hy, gm_sqGen t (𝟙 Y) y i hy.1, gm_sqGen t (𝟙 Y) y j hy.2]
  refine (congrArg (· ^ 2) (gen_trans ht (𝟙 _) y hi hj)).trans ?_
  refine (mul_pow _ _ 2).trans (congrArg (· * _) ?_)
  refine Eq.trans ?_ (gm_linComb (sqLB L) φ ε (𝟙 _) y i j hy.1 hy.2).symm
  rw [trF, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [gm_sq_g L (𝟙 _ ≫ φ k) y (i k) (j k) (by simpa using Set.mem_iInter.1 hi k)
    (by simpa using Set.mem_iInter.1 hj k), ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem val_sqGen {L : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) {z : Z}
    {J : (Z ⟶ X) → Fin 1 → L.ι} (hJ : Good (sqLB L) z J) (r : Z ⟶ Y) :
    val (sqGen L φ ε t) r z J = val t r z (fun ψ => J ψ 0) ^ 2 :=
  gm_sqGen t r z _ (hJ.mem φ r)

theorem good_of_sq {L : LB X} {z : Z} {J : (Z ⟶ X) → Fin 1 → L.ι} (hJ : Good (sqLB L) z J) :
    Good L z (fun ψ => J ψ 0) := fun ψ => mem_sq.1 (hJ ψ)

end GlobalTheory.SqSym

namespace GlobalTheory

open RigidIsoCube SqSym SqLevel in

theorem sq_iso_respects_symmetry_pointwise : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U.symG r z N ^ 2 =
        (∏ k : Fin 2, gv wL (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k) z
          (fun _ => N (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k))
          (fun _ => N' (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k)) ^ (![1, -1] : Fin 2 → ℤ) k) *
        val (L := U'.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U'.symG r z N' ^ 2 := by
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
  have hL : (sqLB U.LG.L).IsLB := DVR.linComb_isLB _ U.LG.isLB _ _
  have hL' : (sqLB U'.LG.L).IsLB := DVR.linComb_isLB _ U'.LG.isLB _ _
  have pg := isoPullId_pgen hw (rfl : 𝟙 G.left = 𝟙 G.left)
  have oi : eSec G ≫ (ι[G]).left = eSec G := by
    have : η[G] ≫ ι[G] = η[G] := by simp
    exact congrArg (fun q => q.left) this
  have key := pmaps_of_section pg hL hL' (φ' := ![(ι[G]).left, 𝟙 G.left]) (φ := ![(ι[G]).left, 𝟙 G.left])
    (ε := ![1, -1]) (sqGen _ _ _ U'.symG) (sqGen_isGen U'.LG.isLB U'.symG_gen) (sqGen _ _ _ U.symG)
    (sqGen_isGen U.LG.isLB U.symG_gen) (fun _ => Category.comp_id _) G.hom (eSec G) (Over.w η[G]) s₁
    fun y J J' hJ hJ' => by
      have a := val_corr (good_of_sq hJ) U.symG_rig (𝟙 _)
      rw [val_pull (good_of_sq hJ), val_one, Category.id_comp] at a
      have b := val_corr (good_of_sq hJ') U'.symG_rig (𝟙 _)
      rw [val_pull (good_of_sq hJ'), val_one, Category.id_comp] at b
      rw [val_sqGen _ hJ, val_sqGen _ hJ', a, b, Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, oi, Category.comp_id]
      simp
  set φ : Fin 2 → (G.left ⟶ G.left) := ![(ι[G]).left, 𝟙 G.left] with hφ
  have m1 : ∀ k, (r ≫ φ k) z ∈ (sqLB U.LG.L).U (fun _ => N (r ≫ φ k)) := fun k => mem_sq.2 (hN _)
  have m2 : ∀ k, (r ≫ φ k) z ∈ (sqLB U'.LG.L).U (fun _ => N' (r ≫ φ k)) := fun k => mem_sq.2 (hN' _)
  have e := key Z r z (fun k _ => N (r ≫ φ k)) (fun k _ => N' (r ≫ φ k)) (fun k => by simpa using m1 k)
    (fun k => by simpa using m2 k)
  have h1 : (r ≫ 𝟙 G.left) z ∈ LB.wchart (sqLB U.LG.L) φ (fun k _ => N (r ≫ φ k)) :=
    Set.mem_iInter.2 fun k => by simpa using m1 k
  have h2 : r z ∈ LB.wchart (sqLB U'.LG.L) φ (fun k _ => N' (r ≫ φ k)) :=
    Set.mem_iInter.2 fun k => by simpa using m2 k
  have e1 := gm_sqGen U.symG (r ≫ 𝟙 G.left) z _ h1
  have e2 := gm_sqGen U'.symG r z _ h2
  simp only [Category.comp_id] at e1 e
  exact e1.symm.trans (e.trans (congrArg₂ (· * ·)
    (Finset.prod_congr rfl fun k _ => by rw [gw_isoPullId wL rfl _ z _ _ (m1 k) (m2 k)]) e2))
end GlobalTheory
