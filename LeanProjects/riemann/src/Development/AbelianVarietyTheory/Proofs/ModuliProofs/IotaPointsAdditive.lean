import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SameUnifRefl
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatTorsionIsomorphism
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj

namespace GlobalTheory.IotaAdditive

open ReciprocityTheory.ChartRestriction.G.DVR

theorem val_eq_of_app_injective {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (h : Y' ⟶ Y)
    (hinj : ∀ U, Function.Injective (h.app U).hom) (t : LB.Gen (LB.LinComb L φ ε))
    (t' : LB.Gen (LB.LinComb L φ' ε')) (hF : FormEq φ ε φ' ε') (ht : t.IsGen) (ht' : t'.IsGen)
    (H : ∀ y J, Good L y J → val t h y J = val t' h y J) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (J)
    (hJ : Good L z J) : val t r z J = val t' r z J := by
  obtain ⟨u, hu, hv⟩ := exists_gen hL hF t ht
  have e : ∀ j, u.s j = t'.s j := fun j => Units.ext (hinj _ (fn_ext fun y hy => by
    choose I hI using fun χ : Y' ⟶ X => exists_chart hL (χ y)
    have hI' : Good L y I := hI
    have hy' : h y ∈ LB.wchart L φ' j := hy
    refine (gs_pull (𝟙 _) h y (LB.wchart L φ' j) hy' _).trans
      (Eq.trans ?_ (gs_pull (𝟙 _) h y (LB.wchart L φ' j) hy' _).symm)
    rw [Category.id_comp]
    refine (gs_unit h y _ hy' _).trans (Eq.trans (congrArg Units.val ?_) (gs_unit h y _ hy' _).symm)
    exact (gen_trans hu h y hy' (hI'.mem φ' h)).trans ((congrArg _ ((hv _ h y I hI').trans (H y I hI'))).trans
      (gen_trans ht' h y hy' (hI'.mem φ' h)).symm)))
  rw [← hv Z r z J hJ]
  exact congrArg (gm r z _) (e _)

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}

theorem restrict_app_injective (W : (Spec (CommRingCat.of R)).Opens) (U : W.toScheme.Opens) :
    Function.Injective ((jK R ∣_ W).app U).hom := by
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    show RingHom.ker (algebraMap R (FractionRing R)) ≤ _
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R _)]; exact bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have : IsSchemeTheoreticallyDominant (jK R ∣_ W) :=
    IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict (jK R) W).flip
  exact (jK R ∣_ W).app_injective U

theorem tau_isGen (ψW : PsiOn D W) (a b : D.X) : (ψW.tau a b).IsGen :=
  mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (ψW.psi_gen _)
    (invGen_isGen _ _ _ _ (ψW.psi_gen _))) (invGen_isGen _ _ _ _ (ψW.psi_gen _)))
    (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _))

theorem val_tau_generic (ψW : PsiOn D W) (a b : D.X) {z : (jK R ⁻¹ᵁ W).toScheme} {J} (hJ : Good D.P.L z J) :
    val (ψW.tau a b) (jK R ∣_ W) z J = val (D.tau a b) (jK R ⁻¹ᵁ W).ι z J := by
  have p : ∀ χ, val (ψW.psi χ) (jK R ∣_ W) z J = val (D.psi χ) (jK R ⁻¹ᵁ W).ι z J := fun χ => by
    have := ((val_pull hJ _ _ _).symm.trans (val_corr hJ (ψW.psi_eq χ) (𝟙 _))).trans (val_pull hJ _ _ _)
    rwa [Category.id_comp, Category.id_comp] at this
  have q : val (D.rigW W) (jK R ∣_ W) z J = val D.rigK (jK R ⁻¹ᵁ W).ι z J :=
    (val_pull hJ _ _ _).trans ((congrArg (fun r => val (L := D.P.L) D.rig r z J)
      (morphismRestrict_ι (jK R) W)).trans (val_pull hJ _ _ _).symm)
  exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (p _) ((val_inv _ _).trans (congrArg (·⁻¹) (p _)))))
    ((val_inv _ _).trans (congrArg (·⁻¹) (p _))))) ((val_inv _ _).trans (congrArg (·⁻¹) q)))).trans
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))).symm

theorem tau_mul (hB : D.TauBimult) (ψW : PsiOn D W) (a a' b : D.X) {T : Over (Spec (CommRingCat.of R))}
    (ρ : T ⟶ TW W) {z : T.left} {J} (hJ : Good D.P.L z J) :
    val (ψW.tau (a + a') b) ρ.left z J * th D z J (cP D T a) (cP D T a') (cP D T b) =
      val (ψW.tau a b) ρ.left z J * val (ψW.tau a' b) ρ.left z J := by
  have key := val_eq_of_app_injective D.P.isLB (jK R ∣_ W) (restrict_app_injective W)
    (LB.mulGen D.P.L _ _ _ _ (ψW.tau (a + a') b) (DegPre.cubAtT D (TW W) (cP D _ a) (cP D _ a') (cP D _ b)))
    (LB.mulGen D.P.L _ _ _ _ (ψW.tau a b) (ψW.tau a' b)) (fun U _ h => ?_)
    (mulGen_isGen _ _ _ _ _ _ _ (tau_isGen ψW _ _) (pullGen_isGen _ _ _ _ D.cub.isGen _))
    (mulGen_isGen _ _ _ _ _ _ _ (tau_isGen ψW _ _) (tau_isGen ψW _ _)) (fun y I hI => ?_) ρ.left z J hJ
  · have e := (val_mul hJ _ _ _).symm.trans (key.trans (val_mul hJ _ _ _))
    refine Eq.trans (congrArg₂ (· * ·) rfl ?_) e
    refine Eq.trans ?_ (val_cub D.cub ρ hJ (cP D _ a) (cP D _ a') (cP D _ b)).symm
    rw [comp_cP, comp_cP, comp_cP]
  · have p : ∀ x y w v : (TW W).left ⟶ D.P.A.left, ∏ i : ((PUnit ⊕ PUnit) ⊕ PUnit) ⊕ PUnit.{1},
        h (Sum.elim (Sum.elim (Sum.elim (fun _ => x) (fun _ => y)) (fun _ => w)) (fun _ => v) i) ^
          Sum.elim (Sum.elim (Sum.elim (fun _ => (-1 : ℤ)) (fun _ => - -1)) (fun _ => - -1)) (fun _ => -1) i =
        (h x)⁻¹ * h y * h w * (h v)⁻¹ := fun x y w v => by
      simp [Fintype.prod_sum_type]
    refine (prod_sum₂ (K' := thK) (U := U) _ (p (cP D _ (a + a' + b)).left (cP D _ (a + a')).left (cP D _ b).left
      (1 : TW W ⟶ D.P.A).left) (prod_cub (T := TW W) (U := U) (cP D _ a) (cP D _ a') (cP D _ b) h)).trans
      (Eq.trans ?_ (prod_sum₂ (U := U) _
        (p (cP D _ (a + b)).left (cP D _ a).left (cP D _ b).left (1 : TW W ⟶ D.P.A).left)
        (p (cP D _ (a' + b)).left (cP D _ a').left (cP D _ b).left (1 : TW W ⟶ D.P.A).left)).symm)
    simp only [cPoint_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · let T' : Over (Spec (CommRingCat.of R)) := Over.mk ((jK R ⁻¹ᵁ W).ι ≫ jK R)
    let κ : T' ⟶ TK R := Over.homMk (jK R ⁻¹ᵁ W).ι rfl
    let σ : T' ⟶ TW W := Over.homMk (jK R ∣_ W) (morphismRestrict_ι (jK R) W)
    have e := (val_mul hI _ _ _).symm.trans ((val_corr hI (hB a a' b) κ.left).trans (val_mul hI _ _ _))
    refine (val_mul hI _ _ _).trans (Eq.trans (congrArg₂ (· * ·) (val_tau_generic ψW _ _ hI) ?_) (e.trans
      ((val_mul hI _ _ _).trans (congrArg₂ (· * ·) (val_tau_generic ψW _ _ hI) (val_tau_generic ψW _ _ hI))).symm))
    refine (val_cub D.cub σ hI (cP D _ a) (cP D _ a') (cP D _ b)).trans
      (Eq.trans ?_ (val_cub D.cub κ hI (cP D _ a) (cP D _ a') (cP D _ b)).symm)
    simp only [comp_cP]

end GlobalTheory.IotaAdditive
