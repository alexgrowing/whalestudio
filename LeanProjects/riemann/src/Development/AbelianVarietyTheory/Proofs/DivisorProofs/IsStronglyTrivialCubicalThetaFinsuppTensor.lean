import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosVec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensBal

section Alg

variable {r : ℕ} {U : Type} [CommGroup U]

theorem prod_theta (a b c : Vec r) (F : Vec r → U) :
    ∏ v ∈ (theta a b c).support, F v ^ theta a b c v =
      F (a + b + c) * (F (a + b))⁻¹ * (F (a + c))⁻¹ * (F (b + c))⁻¹ * F a * F b * F c * (F 0)⁻¹ := by
  have h0 : ∀ v, F v ^ (0 : ℤ) = 1 := fun v => zpow_zero _
  have hadd : ∀ v (m n : ℤ), F v ^ (m + n) = F v ^ m * F v ^ n := fun v m n => zpow_add _ _ _
  change (theta a b c).prod (fun v n => F v ^ n) = _
  simp only [theta, sub_eq_add_neg, ← Finsupp.single_neg, Finsupp.prod_add_index' h0 hadd]
  simp only [Finsupp.prod_single_index (h := fun v (n : ℤ) => F v ^ n) (h0 _), zpow_one, zpow_neg]

end Alg

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem vecHom_add (T : Tens D D' W) (u v : Vec r) : vecHom T (u + v) = vecHom T u * vecHom T v := by
  simp only [vecHom, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  exact mul_mul_mul_comm _ _ _ _

theorem vecHom_zero (T : Tens D D' W) : vecHom T 0 = 1 := by
  simp only [vecHom, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.mul_one]

theorem vecLat_add (T : Tens D D' W) (u v : Vec r) (y y' : D'.X) :
    vecLat T (u + v) y y' = vecLat T u y y' + vecLat T v y y' := by
  simp only [vecLat, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  abel

theorem vecLat_zero (T : Tens D D' W) (y y' : D'.X) : vecLat T 0 y y' = 0 := by
  simp only [vecLat, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]

theorem comp_vecHom (T : Tens D D' W) {Z : Over (Spec (CommRingCat.of R))} (p q : Z ⟶ D'.P.A) (v : Vec r) :
    lift p q ≫ vecHom T v = (∏ k, (p ≫ T.pr k) ^ v (Sum.inl k)) * ∏ k, (q ≫ T.pr k) ^ v (Sum.inr k) := by
  have e := (preHom (G := D.P.A) (lift p q)).map_mul (∏ k, (fst D'.P.A D'.P.A ≫ T.pr k) ^ v (Sum.inl k))
    (∏ k, (snd D'.P.A D'.P.A ≫ T.pr k) ^ v (Sum.inr k))
  simp only [map_prod, map_zpow] at e
  rw [vecHom]
  simpa only [preHom, MonoidHom.mk'_apply, lift_fst_assoc, lift_snd_assoc] using e

theorem zero_vecHom (T : Tens D D' W) (v : Vec r) : lift η[D'.P.A] η[D'.P.A] ≫ vecHom T v = 1 := by
  have h : ∀ k, η[D'.P.A] ≫ T.pr k = 1 := fun k => by
    haveI := T.pr_hom k
    rw [IsMonHom.one_hom, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  simp only [comp_vecHom, h, one_zpow, Finset.prod_const_one, _root_.mul_one]

def cPHom (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) : Multiplicative D.X →* (T ⟶ D.P.A) :=
  MonoidHom.mk' (fun x => DVR.cP D T x.toAdd) fun a b => DVR.cPoint_add D T a.toAdd b.toAdd

theorem pt_vecHom (T : Tens D D' W) (y y' : D'.X) (v : Vec r) :
    lift (DVR.cP D' (TK R) y) (DVR.cP D' (TK R) y') ≫ vecHom T v = DVR.cP D (TK R) (vecLat T v y y') := by
  have hp : ∀ x k, DVR.cP D' (TK R) x ≫ T.pr k = cPHom D (TK R) (Multiplicative.ofAdd (T.xe x k)) := fun x k => by
    simp only [DVR.cP, Category.assoc, T.c_pr]; rfl
  rw [comp_vecHom, show DVR.cP D (TK R) (vecLat T v y y') = cPHom D (TK R) (Multiplicative.ofAdd (vecLat T v y y')) from rfl]
  simp only [hp, vecLat, ofAdd_add, ofAdd_sum, ofAdd_zsmul, map_mul, map_prod, map_zpow]

theorem cubV_psi (hB : D.TauBimult) {z : (TK R).left} {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : Good D.P.L z J) (p q s : D.X) :
    cubV D.cub (T := TK R) z J (DVR.cP D _ p) (DVR.cP D _ q) (DVR.cP D _ s) =
      (val (D.psi (p + q + s)) (𝟙 _) z J)⁻¹ * val (D.psi (p + q)) (𝟙 _) z J * val (D.psi (p + s)) (𝟙 _) z J *
        val (D.psi (q + s)) (𝟙 _) z J * (val (D.psi p) (𝟙 _) z J)⁻¹ * (val (D.psi q) (𝟙 _) z J)⁻¹ *
        (val (D.psi s) (𝟙 _) z J)⁻¹ * val (D.psi 0) (𝟙 _) z J := by
  have t := DVR.tauK_mul hJ hB p q s
  have t0 := GlobalTheory.TauBalElem.tau_zero_left hB hJ 0
  rw [GlobalTheory.TauBalBox.tau_val D hJ, GlobalTheory.TauBalBox.tau_val D hJ, GlobalTheory.TauBalBox.tau_val D hJ] at t
  rw [GlobalTheory.TauBalBox.tau_val D hJ, add_zero] at t0
  apply Additive.ofMul.injective
  have t' := congrArg Additive.ofMul t
  have t0' := congrArg Additive.ofMul t0
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at t' t0' ⊢
  linear_combination (norm := abel) t' + t0'

theorem triv_theta : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W), D.TauBimult → ∀ a b c : GlobalTheory.TensBal.Vec r, GlobalTheory.TensBal.Triv T (GlobalTheory.TensBal.theta a b c) := by
  intro R _ _ D D' r W T hB a b c
  have hF : FormEq (fun I => (lift (vecHom T a) (lift (vecHom T b) (vecHom T c))).left ≫ thφ D.P.A (x3 D.P.A) I) thε
      (fun v : (theta a b c).support => (vecHom T v.1).left) (fun v => theta a b c v.1) := fun U _ h => by
    refine (prod_cub (vecHom T a) (vecHom T b) (vecHom T c) h).trans ?_
    rw [Finset.prod_coe_sort (theta a b c).support (fun v => h (vecHom T v).left ^ theta a b c v), prod_theta,
      vecHom_add, vecHom_add, vecHom_add, vecHom_add, vecHom_zero]
  obtain ⟨Ξ, hΞ, hv⟩ := exists_gen D.P.isLB hF
    (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift (vecHom T a) (lift (vecHom T b) (vecHom T c))).left)
    (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _)
  refine ⟨Ξ, hΞ, fun z J hJ => ?_, fun z J hJ y y' => ?_⟩
  · refine (hv _ _ z J hJ).trans ((val_cub D.cub (lift η[D'.P.A] η[D'.P.A]) hJ _ _ _).trans ?_)
    rw [zero_vecHom, zero_vecHom, zero_vecHom]
    exact (isCub_cubV D.cub hJ).face _ _
  · refine (hv _ _ z J hJ).trans ((val_cub D.cub (lift (DVR.cP D' (TK R) y) (DVR.cP D' (TK R) y')) hJ _ _ _).trans ?_)
    rw [pt_vecHom, pt_vecHom, pt_vecHom, cubV_psi hB hJ]
    simp only [zpow_neg, ← inv_zpow]
    rw [prod_theta (F := fun v => (val (D.psi (vecLat T v y y')) (𝟙 _) z J)⁻¹)]
    rw [vecLat_add T (a + b) c, vecLat_add T a b, vecLat_add T a c, vecLat_add T b c, vecLat_zero]
    simp only [inv_inv]

end GlobalTheory.TensBal
