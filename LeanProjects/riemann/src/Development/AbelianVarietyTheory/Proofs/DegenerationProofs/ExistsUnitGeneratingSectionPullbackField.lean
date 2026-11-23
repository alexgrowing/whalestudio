import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQkPullEquiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEquivOfIsPushout
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamFieldPull
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenSecField

open GlobalTheory.IndivisibleSection ReciprocityTheory.ChartRestriction.G.DVR

theorem flat_of_injective {R K : Type} [CommRing R] [IsDomain R] [Field K] {φ : R →+* K}
    (hφ : Function.Injective φ) : φ.Flat := by
  have e : φ = (IsFractionRing.lift (A := R) (K := FractionRing R) hφ).comp (algebraMap R (FractionRing R)) :=
    RingHom.ext fun x => (IsFractionRing.lift_algebraMap hφ x).symm
  rw [e]
  refine RingHom.Flat.comp ?_ ?_
  · exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  · let _ := (IsFractionRing.lift (A := R) (K := FractionRing R) hφ).toAlgebra
    exact (inferInstance : Module.Flat (FractionRing R) K)

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'}

theorem exists_pow_one (u : LB.Sec L) : ∃ s : H0 L 1, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) J, Good L z J →
    sval s r z J = gs r z _ (u.f (J r)) := by
  have le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0) :=
    fun j y hy => Set.mem_iInter.1 hy 0
  refine ⟨⟨fun j => (X.presheaf.map (homOfLE (le j)).op).hom (u.f (j 0)), fun j j' => fn_ext fun y hy => ?_⟩,
    fun Z r z J hJ => ?_⟩
  · refine (gs_res (𝟙 X) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 X) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 X) y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 X) y j j' hy.1 hy.2)))
      (gs_res (𝟙 X) y _ hy _))).symm)
    refine (gs_res (𝟙 X) y (le j) hy.1 _).trans ((FlatSec.gs_sec_trans u (𝟙 X) y (le j hy.1) (le j' hy.2)).trans
      (congrArg₂ (· * ·) (congrArg Units.val ?_) (gs_res (𝟙 X) y (le j') hy.2 _).symm))
    simp
  · rw [sval_of _ r z J (fun _ => J r) (fun _ => by rw [Category.comp_id])]
    exact gs_res r z (le fun _ => J r) (Set.mem_iInter.2 fun _ => hJ r) _

theorem cst_zero' {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Sp R) (z : Z) : cst q z 0 = 0 := by
  rw [cst, map_zero, gs_eq q z ⊤ trivial, map_zero, map_zero]

theorem sval_eq_zero {R R' : Type} [CommRing R] [CommRing R'] {g : R →+* R'} (hg : g.Flat) [CompactSpace X]
    [QuasiSeparatedSpace X] {f : X ⟶ Sp R} {π : X' ⟶ X} {f' : X' ⟶ Sp R'}
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull π)} (hw : w.IsGen) {th : H0 L 1} (hth : ∀ s : H0 L 1, ∃ a, SecIsMul f a s th)
    (h₀ : ∀ y J, Good L y J → sval th π y J = 0) (s : H0 L' 1) (y : X') {J'} (hJ' : Good L' y J') :
    sval s (𝟙 X') y J' = 0 := by
  obtain ⟨t, ht⟩ := exists_sec hL' (φ' := fun _ : PUnit => 𝟙 X') (ε' := fun _ => 1)
    (fun U _ h => by simp) s
  obtain ⟨σ, hσ⟩ := ArcPull.exists_up_sec ((isGen_iff w).1 hw) hL hL' (fun _ : PUnit => 𝟙 X') (fun _ => π)
    (fun _ => 1) (𝟙 X') (fun _ => by simp) t
  obtain ⟨n, c, u, hu⟩ := FlatSec.exists_comb_of_flat R R' g hg X f X' π f' H L hL σ
  obtain ⟨J, hJ⟩ := DegPull.exists_good' hL y
  have e := hσ _ (𝟙 X') y J J' hJ hJ'
  rw [ht _ _ y J' hJ', sval_of σ _ y J (fun _ => J π) (fun _ => by rw [Category.id_comp]), Category.id_comp] at e
  have z : ∀ i, gs π y _ ((u i).f (J π)) = 0 := fun i => by
    obtain ⟨v, hv⟩ := exists_pow_one (u i)
    obtain ⟨a, ha⟩ := hth v
    rw [← hv _ π y J hJ, sval_of_secIsMul ha π y hJ, h₀ y J hJ, mul_zero]
  have e' := (hu y (J π) (hJ π)).symm.trans e
  simp only [z, mul_zero, Finset.sum_const_zero] at e'
  exact (Units.mul_right_eq_zero _).1 e'.symm

end GlobalTheory.GenSecField

namespace GlobalTheory

open GlobalTheory.IndivisibleSection ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.GenSecField in

theorem exists_unit_generating_section_pull : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (φ : R →+* K), Function.Injective φ → ∀ (D : DegPre R) (D' : DegPre K) (hD : IsPullDeg φ D D') (th : H0 D.P.L 1) (th' : H0 D'.P.L 1), (∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j) → (∀ s : H0 D'.P.L 1, ∃ r : K, ∀ j, s.f j = resTop _ (scal D'.P.A.hom r) * th'.f j) → ∃ c : Kˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → sval th (r ≫ PsiEvenPull.proj hD) z J = (TauTwist.unitAt (r ≫ D'.P.A.hom) z c * ArcPull.om hD.w z J J' r).val * sval th' r z J' := by
  intro R K _ _ _ φ hφ D D' hD th th' hth hth'
  have hc : ∀ _ : Fin 1, 𝟙 D'.P.A.left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ 𝟙 D.P.A.left :=
    fun _ => (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨a, ha, -⟩ := SecPull.existsUnique_secPull _ _ _ _ D.P.L D'.P.L _ D.P.isLB D'.P.isLB hD.w hD.w_gen (Fin 1)
    (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)) (PsiEvenPull.proj hD) hc th
  obtain ⟨c, hac⟩ := hth' a
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      sval th (r ≫ PsiEvenPull.proj hD) z J =
        cst (r ≫ D'.P.A.hom) z c * (ArcPull.om hD.w z J J' r).val * sval th' r z J' := fun Z r z J J' hJ hJ' => by
    have e := FamFieldPull.IsSecPull.val ha hc r z hJ hJ'
    rw [sval_of_secIsMul (p := D'.P.A.hom) hac r z hJ', Fin.prod_univ_one, Category.comp_id, zpow_natCast,
      pow_one] at e
    exact e.trans ((mul_left_comm _ _ _).trans (_root_.mul_assoc _ _ _).symm)
  by_cases h : c = 0
  · subst h
    have : IsProper D.P.A.hom := D.P.isAb.proper
    have : CompactSpace D.P.A.left := QuasiCompact.compactSpace_of_compactSpace D.P.A.hom
    have : QuasiSeparatedSpace D.P.A.left := quasiSeparatedSpace_of_quasiSeparated D.P.A.hom
    have h₀ : SecIsMul D'.P.A.hom (0 : K) th' th' := secIsMul_of_sval D'.P.isLB fun y J' hJ' => by
      rw [cst_zero', zero_mul]
      refine sval_eq_zero (flat_of_injective hφ) (pull_grp hD).1 D.P.isLB D'.P.isLB hD.w_gen hth
        (fun x J hJ => ?_) th' y hJ'
      obtain ⟨I, hI⟩ := DegPull.exists_good' D'.P.isLB x
      have e := key _ (𝟙 _) x J I hJ hI
      rwa [Category.id_comp, cst_zero', zero_mul, zero_mul] at e
    refine ⟨1, fun Z r z J J' hJ hJ' => ?_⟩
    rw [key Z r z J J' hJ hJ', sval_of_secIsMul h₀ r z hJ', cst_zero', zero_mul, zero_mul, zero_mul, mul_zero]
  · refine ⟨Units.mk0 c h, fun Z r z J J' hJ hJ' => ?_⟩
    rw [key Z r z J J' hJ hJ', Units.val_mul, TauTwist.unitAt_val]
    rfl

end GlobalTheory
