import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkOfInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem stalkOf_cpt_bijective (W : Type) [CommRing W] [IsLocalRing W] : Function.Bijective (stalkOf (cpt W)) := by
  have e : stalkOf (cpt W) = (stalkClosedPointIso (.of W)).inv.hom := by
    have h := ΓSpecIso_hom_stalkClosedPointIso_inv (CommRingCat.of W)
    have h' : (stalkClosedPointIso (.of W)).inv = (Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫
        (Sp W).presheaf.germ ⊤ (cpt W) trivial := by
      rw [Iso.eq_inv_comp]; exact h
    rw [h']; rfl
  rw [e]
  exact (stalkClosedPointIso (.of W)).symm.commRingCatIsoToRingEquiv.bijective

theorem exists_unit_stalkOf (W : Type) [CommRing W] [IsLocalRing W] (x : ((Sp W).presheaf.stalk (cpt W))ˣ) :
    ∃ ε : Wˣ, stalkOf (cpt W) (ε : W) = x.val := by
  let e := RingEquiv.ofBijective _ (stalkOf_cpt_bijective W)
  exact ⟨Units.map e.symm.toMonoidHom x, e.apply_symm_apply x.val⟩

theorem gs_scal_section {W : Type} [CommRing W] {Y : Scheme.{0}} (p : Y ⟶ Sp W) (e : Sp W ⟶ Y) (he : e ≫ p = 𝟙 _)
    (z : Sp W) (u : W) : gs e z ⊤ (scal p u) = stalkOf z u := by
  have h := gs_pull e p z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom u)
  rw [he] at h
  exact h.trans (gs_eq (𝟙 _) z ⊤ trivial _)

theorem gw_val_indep {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    (hw : w.IsGen) {s : Y ⟶ X} {s' : Y' ⟶ X'} (t : LB.Gen (L.pull s)) (ht : t.IsGen) (t' : LB.Gen (L'.pull s'))
    (ht' : t'.IsGen) (r : Z ⟶ Y) (r' : Z ⟶ Y') (e : Z ⟶ X') (he' : r' ≫ s' = e) (he : r ≫ s = e ≫ F) (z : Z)
    {I J : (Z ⟶ X) → L.ι} {I' J' : (Z ⟶ X') → L'.ι} (hI : Good L z I) (hJ : Good L z J) (hI' : Good L' z I')
    (hJ' : Good L' z J') :
    gw w e z (J (e ≫ F)) (J' e) * val t' r' z J' * (val t r z J)⁻¹ =
      gw w e z (I (e ≫ F)) (I' e) * val t' r' z I' * (val t r z I)⁻¹ := by
  have a := (isGen_iff w).1 hw Z e z (J (e ≫ F)) (I (e ≫ F)) (J' e) (I' e) (hJ (e ≫ F)) (hI (e ≫ F)) (hJ' e) (hI' e)
  have b : val t r z J = _ * val t r z I := gen_trans ht r z (hJ.mem _ r) (hI.mem _ r)
  have c : val t' r' z J' = _ * val t' r' z I' := gen_trans ht' r' z (hJ'.mem _ r') (hI'.mem _ r')
  rw [trF, Fintype.prod_unique, zpow_one] at b c
  subst he'
  rw [he] at b
  rw [a, b, c]
  generalize gm ((r' ≫ s') ≫ F) z _ _ = A
  generalize gm (r' ≫ s') z _ _ = B
  rw [mul_inv]
  generalize gw w _ _ _ _ = C
  generalize val t' r' z I' = D
  generalize (val t r z I)⁻¹ = E
  have : A * B⁻¹ * C * (B * D) * (A⁻¹ * E) = (A * A⁻¹) * (B * B⁻¹) * (C * D * E) := by ac_rfl
  rw [this]; simp

theorem Trait.carries_unit : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (u : W) (σ' : H0 T.U.LG.L k) (σ : SecK C.P.L.L T.β k), T.Carries u σ' σ → ∃ ε : Wˣ, ∀ J J', Good C.P.L.L (cpt W) J → Good T.U.LG.L (cpt W) J' → sval σ (unitW T.G) (cpt W) J * (val T.U.LG.rig (idW W) (cpt W) J').val ^ k = stalkOf (cpt W) (u * ε) * sval σ' (unitW T.G) (cpt W) J' * (val C.P.L.rig T.ξ (cpt W) J).val ^ k := by
  intro R _ _ _ D C W _ _ _ T k u σ' σ h
  obtain ⟨I, hI, -⟩ := exists_good C.P.L.L C.P.L.isLB (cpt W) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  obtain ⟨I', hI', -⟩ := exists_good T.U.LG.L T.U.LG.isLB (cpt W) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  have he : T.ξ ≫ eSec C.G = unitW T.G ≫ T.β := (PullGtPf.IsGrpPullback.one_left T.cart).symm
  obtain ⟨ε, hε⟩ := exists_unit_stalkOf W ((gw T.ℓ (unitW T.G) (cpt W) (I (unitW T.G ≫ T.β)) (I' (unitW T.G)) *
    val T.U.LG.rig (idW W) (cpt W) I' * (val C.P.L.rig T.ξ (cpt W) I)⁻¹) ^ k)
  refine ⟨ε, fun J J' hJ hJ' => ?_⟩
  have key := gw_val_indep T.ℓ T.ℓ_gen C.P.L.rig C.P.L.rigGen T.U.LG.rig T.U.LG.rigGen T.ξ (idW W) (unitW T.G)
    (Category.id_comp _) he (cpt W) hI hJ hI' hJ'
  rw [← key] at hε
  rw [h _ (unitW T.G) (cpt W) J J' hJ hJ', gs_scal_section T.G.hom (unitW T.G) (Over.w η[T.G]), map_mul, hε]
  generalize gw T.ℓ _ _ _ _ = A
  generalize val T.U.LG.rig _ _ _ = B
  generalize val C.P.L.rig _ _ _ = E
  have : (A * B * E⁻¹) ^ k * E ^ k = A ^ k * B ^ k := by rw [← mul_pow, ← mul_pow, inv_mul_cancel_right]
  have := congrArg Units.val this
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at this ⊢
  linear_combination (-(stalkOf (cpt W) u * sval σ' (unitW T.G) (cpt W) J')) * this

end GlobalTheory.Mum
