import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsTranslatedPullOfIsTransPull
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSymmetricLiftOddOrderLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.WeilRos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.MixCore

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CommPairing (tval translT_fst)
open GlobalTheory.ThetaAct (sv sv_ext sv_add sv_smul translT_translT translT_one translT_snd translPt_one)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaLaw

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

section Twist

variable {L : LB A.left} (hL : L.IsLB) {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} (hm : ψ ≫ snd T A = m)
  (hψ : ψ ≫ fst T A = fst T A) {a b : ℤ}
  (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])) (hα : α.IsGen)

def twistFun (v : SecM A L b T) : SecM A L a T :=
  SecM.ofSec A (VVRank.exists_isTwistPull A (hm := hm) hL hα (SecM.toSec A v)).choose

theorem sv_twistFun (v : SecM A L b T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    sv (twistFun hL hm α hα v) r z J = (val α r z J).val * sv v (r ≫ ψ.left) z J :=
  VVRank.sv_of_isTwistPull A (VVRank.exists_isTwistPull A (hm := hm) hL hα (SecM.toSec A v)).choose_spec r z hJ

def twist : SecM A L b T →ₗ[Γ(T.left, ⊤)] SecM A L a T where
  toFun := twistFun hL hm α hα
  map_add' v w := sv_ext hL fun y J hJ => by
    rw [sv_add _ _ _ _ hJ, sv_twistFun _ _ _ _ _ _ _ hJ, sv_twistFun _ _ _ _ _ _ _ hJ, sv_twistFun _ _ _ _ _ _ _ hJ,
      sv_add _ _ _ _ hJ, mul_add]
  map_smul' c v := sv_ext hL fun y J hJ => by
    have e : ψ.left ≫ (fst T A).left = (fst T A).left := by rw [← Over.comp_left, hψ]
    rw [RingHom.id_apply, sv_smul _ (twistFun hL hm α hα v) _ _ hJ, sv_twistFun _ _ _ _ _ _ _ hJ,
      sv_twistFun _ _ _ _ _ _ _ hJ, sv_smul _ v _ _ hJ, Category.assoc, e, mul_left_comm]

theorem sv_twist (v : SecM A L b T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    sv (twist hL hm hψ α hα v) r z J = (val α r z J).val * sv v (r ≫ ψ.left) z J :=
  sv_twistFun hL hm α hα v r z hJ

end Twist

section Group

variable {k : ℤ} {T : Over S}

theorem gen_ext {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u (𝟙 _) y J = val u' (𝟙 _) y J) : u = u' := by
  have e := sec_ext_val hM (s := genSec u hu) (s' := genSec u' hu') fun y J hJ => by
    rw [sval_genSec _ _ _ _ hJ, sval_genSec _ _ _ _ hJ, h y J hJ]
  cases u; cases u'
  exact congrArg _ (funext fun j => Units.ext (e j))

theorem ext {L : LB A.left} (hL : L.IsLB) {θ θ' : ThetaGrp A L k T} (h : θ.pt = θ'.pt)
    (hv : ∀ y J, Good L y J → tval θ (𝟙 _) y J = tval θ' (𝟙 _) y J) : θ = θ' := by
  obtain ⟨a, u, hu⟩ := θ
  obtain ⟨a', u', hu'⟩ := θ'
  obtain rfl : a = a' := h
  obtain rfl : u = u' := gen_ext hL hu hu' hv
  rfl

theorem exists_scalar {L : LB A.left} (hL : L.IsLB) (k : ℤ) (c : Γ(T.left, ⊤)ˣ) :
    ∃ θ : ThetaGrp A L k T, θ.pt = 1 ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J),
      Good L z J → tval θ r z J = gm (r ≫ (fst T A).left) z ⊤ c := by
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (translPt A (1 : T ⟶ A)).left]) (ε' := ![k, -k])
    (fun U _ f => by
      refine (Fintype.prod_empty _).trans ?_
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, translPt_one, mul_inv_cancel])
    (constGen A L c) (isGen_of_gm _ fun y j j' h h' => by
      obtain rfl : j = j' := Subsingleton.elim _ _
      rw [trF, Fintype.prod_empty, _root_.one_mul])
  exact ⟨⟨1, t, ht⟩, rfl, fun Z r z J hJ => (hv Z r z J hJ).trans (H1.val_constGen L c r z J)⟩

variable {L : RigLB A}

instance : One (ThetaGrp A L.L k T) := ⟨(exists_scalar L.isLB k 1).choose⟩

instance : Mul (ThetaGrp A L.L k T) := ⟨fun θ θ' => (ThetaAct.exists_mul L.isLB θ θ').choose⟩

instance : Inv (ThetaGrp A L.L k T) := ⟨fun θ => (ThetaAct.exists_inv L.isLB θ).choose⟩

theorem pt_one : (1 : ThetaGrp A L.L k T).pt = 1 := (exists_scalar L.isLB k 1).choose_spec.1

theorem pt_mul' (θ θ' : ThetaGrp A L.L k T) : (θ * θ').pt = θ'.pt * θ.pt :=
  (ThetaAct.exists_mul L.isLB θ θ').choose_spec.1

theorem pt_inv (θ : ThetaGrp A L.L k T) : θ⁻¹.pt = θ.pt⁻¹ := (ThetaAct.exists_inv L.isLB θ).choose_spec.1

section Val

variable {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J : (Z ⟶ A.left) → L.L.ι} (hJ : Good L.L z J)
include hJ

theorem tval_one : tval (1 : ThetaGrp A L.L k T) r z J = 1 :=
  ((exists_scalar L.isLB k 1).choose_spec.2 Z r z J hJ).trans (map_one _)

theorem tval_mul (θ θ' : ThetaGrp A L.L k T) :
    tval (θ * θ') r z J = tval θ r z J * tval θ' (r ≫ (translT A θ.pt).left) z J :=
  (ThetaAct.exists_mul L.isLB θ θ').choose_spec.2 Z r z J hJ

theorem tval_inv (θ : ThetaGrp A L.L k T) : tval θ⁻¹ r z J = (tval θ (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹ :=
  (ThetaAct.exists_inv L.isLB θ).choose_spec.2 Z r z J hJ

end Val

instance group : Group (ThetaGrp A L.L k T) :=
  Group.ofLeftAxioms
    (fun a b c => ext L.isLB (by simp only [pt_mul', _root_.mul_assoc]) fun y J hJ => by
      simp only [tval_mul _ _ hJ, pt_mul', Category.assoc, translT_translT, _root_.mul_assoc])
    (fun a => ext L.isLB (by rw [pt_mul', pt_one, _root_.mul_one]) fun y J hJ => by
      rw [tval_mul _ _ hJ, tval_one _ _ hJ, pt_one, translT_one, Category.comp_id, _root_.one_mul])
    (fun a => ext L.isLB (by rw [pt_mul', pt_inv, pt_one, mul_inv_cancel]) fun y J hJ => by
      rw [tval_mul _ _ hJ, tval_inv _ _ hJ, tval_one _ _ hJ, pt_inv, inv_mul_cancel])

variable (L k T)

def scalar : Γ(T.left, ⊤)ˣ →* ThetaGrp A L.L k T :=
  MonoidHom.mk' (fun c => (exists_scalar L.isLB k c).choose) fun c d => by
    have p := fun c => (exists_scalar (T := T) L.isLB k c).choose_spec
    refine ext L.isLB (by rw [pt_mul', (p _).1, (p _).1, (p _).1, _root_.mul_one]) fun y J hJ => ?_
    rw [tval_mul _ _ hJ, (p _).2 _ _ _ _ hJ, (p _).2 _ _ _ _ hJ, (p _).2 _ _ _ _ hJ, Category.assoc, translT_fst, map_mul]

def op {L : RigLB A} {k : ℤ} {T : Over S} (θ : ThetaGrp A L.L k T) : Module.End Γ(T.left, ⊤) (SecM A L.L k T) :=
  twist L.isLB (ψ := translT A θ.pt) (lift_snd _ _) (lift_fst _ _) θ.φ θ.isGen

theorem sv_op {L : RigLB A} {k : ℤ} {T : Over S} (θ : ThetaGrp A L.L k T) (v : SecM A L.L k T) {Z : Scheme.{0}}
    (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L.L z J) :
    sv (op θ v) r z J = (tval θ r z J).val * sv v (r ≫ (translT A θ.pt).left) z J :=
  sv_twist L.isLB _ _ θ.φ θ.isGen v r z hJ

def action : ThetaGrp A L.L k T →* Module.End Γ(T.left, ⊤) (SecM A L.L k T) where
  toFun := op
  map_one' := LinearMap.ext fun v => sv_ext L.isLB fun y J hJ => by
    rw [sv_op _ _ _ _ hJ, tval_one _ _ hJ, pt_one, translT_one, Category.comp_id, Units.val_one, _root_.one_mul]; rfl
  map_mul' a b := LinearMap.ext fun v => sv_ext L.isLB fun y J hJ => by
    rw [Module.End.mul_apply, sv_op _ _ _ _ hJ, sv_op _ _ _ _ hJ, sv_op _ _ _ _ hJ, tval_mul _ _ hJ, pt_mul', Category.assoc,
      translT_translT, Units.val_mul, _root_.mul_assoc]

variable {L k T}

theorem pt_scalar (c : Γ(T.left, ⊤)ˣ) : (scalar k T L c).pt = 1 := (exists_scalar L.isLB k c).choose_spec.1

theorem tval_scalar (c : Γ(T.left, ⊤)ˣ) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L.L z J) :
    tval (scalar k T L c) r z J = gm (r ≫ (fst T A).left) z ⊤ c := (exists_scalar L.isLB k c).choose_spec.2 Z r z J hJ

theorem scalar_comm (c : Γ(T.left, ⊤)ˣ) (θ : ThetaGrp A L.L k T) : scalar k T L c * θ = θ * scalar k T L c :=
  ext L.isLB (by rw [pt_mul', pt_mul', pt_scalar, _root_.mul_one, _root_.one_mul]) fun y J hJ => by
    rw [tval_mul _ _ hJ, tval_mul _ _ hJ, tval_scalar _ _ _ hJ, tval_scalar _ _ _ hJ, pt_scalar, translT_one,
      Category.comp_id, Category.assoc, translT_fst, mul_comm]

theorem scalar_injective : Function.Injective (scalar k T L) := fun c d h => by
  refine unit_ext fun y _ => ?_
  choose J hJ using fun χ : T.left ⟶ A.left => exists_chart L.isLB (χ y)
  have e : (ptSecT A (1 : T ⟶ A)).left ≫ (fst T A).left = 𝟙 _ := by rw [← Over.comp_left, ptSecT, lift_fst]; rfl
  have a := tval_scalar (k := k) c (ptSecT A (1 : T ⟶ A)).left y hJ
  have b := tval_scalar (k := k) d (ptSecT A (1 : T ⟶ A)).left y hJ
  rw [e] at a b
  rw [← a, ← b, h]

theorem action_scalar (c : Γ(T.left, ⊤)ˣ) (v : SecM A L.L k T) : action k T L (scalar k T L c) v = c.val • v :=
  sv_ext L.isLB fun y J hJ => by
    refine (sv_op _ _ _ _ hJ).trans ?_
    rw [sv_smul _ _ _ _ hJ, tval_scalar _ _ _ hJ, pt_scalar, translT_one, Category.comp_id, gs_unit _ _ ⊤ trivial]

theorem exists_scalar_eq (hp : Function.Surjective (fst T A).left.appTop.hom) {θ : ThetaGrp A L.L k T} (h : θ.pt = 1) :
    ∃ c, scalar k T L c = θ := by
  obtain ⟨c, hc⟩ := SymLiftConst.exists_constT hp L.isLB (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k])
    (fun U _ f => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, h, translPt_one, mul_inv_cancel])
    θ.isGen
  refine ⟨c, ext L.isLB ((pt_scalar c).trans h.symm) fun y J hJ => ?_⟩
  have e := hc (snd T A) y J hJ
  rw [lift_fst_snd] at e
  rw [tval_scalar _ _ _ hJ, Category.id_comp]
  exact e.symm

variable [IsCommMonObj A]

theorem pt_mul (θ θ' : ThetaGrp A L.L k T) : (θ * θ').pt = θ.pt * θ'.pt := (pt_mul' θ θ').trans (mul_comm _ _)

variable (L k T) in

def ptHom : ThetaGrp A L.L k T →* (T ⟶ A) := MonoidHom.mk' ThetaGrp.pt pt_mul

def nval (ν : LB.Gen (negLB A L.L k T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  val (L := L.L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν r z J

omit [IsCommMonObj A] in

theorem negT_snd : (negT A T).left ≫ (snd T A).left = (snd T A ≫ (GrpObj.inv : A ⟶ A)).left := by
  rw [← Over.comp_left, negT, lift_snd]

omit [IsCommMonObj A] in

theorem negT_fst : (negT A T).left ≫ (fst T A).left = (fst T A).left := by
  rw [← Over.comp_left, negT, lift_fst]

omit [IsCommMonObj A] in

theorem negT_negT : (negT A T).left ≫ (negT A T).left = 𝟙 _ := by
  have e : snd T A ≫ (GrpObj.inv : A ⟶ A) = (snd T A)⁻¹ := rfl
  rw [← Over.comp_left, negT, comp_lift, lift_fst, e, GrpObj.comp_inv, lift_snd, inv_inv, lift_fst_snd]; rfl

theorem translT_negT (x : T ⟶ A) : (translT A x).left ≫ (negT A T).left = (negT A T).left ≫ (translT A x⁻¹).left := by
  have e : snd T A ≫ (GrpObj.inv : A ⟶ A) = (snd T A)⁻¹ := rfl
  rw [← Over.comp_left, ← Over.comp_left, negT, e, lift_transl, comp_lift, translT, lift_fst, GrpObj.comp_inv, lift_snd,
    translPt_eq, mul_inv, GrpObj.comp_inv]

theorem exists_conj (ν : LB.Gen (negLB A L.L k T)) (hν : ν.IsGen) (θ : ThetaGrp A L.L k T) :
    ∃ θ' : ThetaGrp A L.L k T, θ'.pt = θ.pt⁻¹ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L.L z J →
      tval θ' r z J = nval ν r z J * (tval θ (r ≫ (negT A T).left) z J * (nval ν (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹) := by
  have e₁ : (negT A T).left ≫ (translPt A θ.pt).left =
      (translT A θ.pt⁻¹).left ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left := by
    rw [← negT_snd, ← Category.assoc, translT_negT, inv_inv, Category.assoc, translT_snd]
  obtain ⟨t, ht, hv⟩ := exists_gen L.isLB (φ' := ![(snd T A).left, (translPt A θ.pt⁻¹).left]) (ε' := ![k, -k])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
        Matrix.cons_val_one, negT_snd, translT_snd, e₁]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L.L ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] ![k, -k] _ _ ν (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ (negT A T).left)
      (LB.invGen L.L _ _ (LB.pullGen L.L ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] ![k, -k] ν
        (translT A θ.pt⁻¹).left))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hν (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ θ.isGen _)
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hν _))))
  exact ⟨⟨_, t, ht⟩, rfl, fun Z r z J hJ => (hv Z r z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _)
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _)))))))⟩

def conj (ν : LB.Gen (negLB A L.L k T)) (hν : ν.IsGen) : ThetaGrp A L.L k T →* ThetaGrp A L.L k T :=
  MonoidHom.mk' (fun θ => (exists_conj ν hν θ).choose) fun a b => by
    have p := fun θ => (exists_conj ν hν θ).choose_spec
    refine ext L.isLB ((p _).1.trans (Eq.trans ?_ (pt_mul _ _).symm)) fun y J hJ => ?_
    · rw [(p _).1, (p _).1, pt_mul, mul_inv]
    rw [tval_mul _ _ hJ, (p _).2 _ _ _ _ hJ, (p _).2 _ _ _ _ hJ, (p _).2 _ _ _ _ hJ, (p _).1, tval_mul _ _ hJ, pt_mul]
    simp only [Category.assoc, translT_negT, translT_translT, inv_inv, mul_inv_rev]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

section Conj

variable (ν : LB.Gen (negLB A L.L k T)) (hν : ν.IsGen)

theorem pt_conj (θ : ThetaGrp A L.L k T) : (conj ν hν θ).pt = θ.pt⁻¹ := (exists_conj ν hν θ).choose_spec.1

theorem tval_conj (θ : ThetaGrp A L.L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L.L z J) :
    tval (conj ν hν θ) r z J =
      nval ν r z J * (tval θ (r ≫ (negT A T).left) z J * (nval ν (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹) :=
  (exists_conj ν hν θ).choose_spec.2 Z r z J hJ

theorem conj_scalar (c : Γ(T.left, ⊤)ˣ) : conj ν hν (scalar k T L c) = scalar k T L c :=
  ext L.isLB (by rw [pt_conj, pt_scalar, inv_one]) fun y J hJ => by
    rw [tval_conj _ _ _ _ _ hJ, tval_scalar _ _ _ hJ, tval_scalar _ _ _ hJ, pt_scalar, inv_one, translT_one,
      Category.comp_id, Category.assoc, negT_fst, mul_inv_cancel_comm_assoc]

def negOp : Module.End Γ(T.left, ⊤) (SecM A L.L k T) :=
  twist L.isLB (ψ := negT A T) (lift_snd _ _) (lift_fst _ _) ν hν

variable (hp : Function.Surjective (fst T A).left.appTop.hom)
include hp

theorem conj_conj (θ : ThetaGrp A L.L k T) : conj ν hν (conj ν hν θ) = θ :=
  ext L.isLB (by rw [pt_conj, pt_conj, inv_inv]) fun y J hJ => by
    have e₁ : (negT A T).left ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left = (snd T A).left := by
      rw [← negT_snd, ← Category.assoc, negT_negT, Category.id_comp]
    obtain ⟨a, ha⟩ := H1.exists_const L.L L.isLB (fst T A).left hp
      (LB.mulGen L.L ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] ![k, -k] _ _ ν
        (LB.pullGen L.L ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] ![k, -k] ν (negT A T).left))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ hν (DVR.pullGen_isGen _ _ _ _ hν _)) (fun U _ f => by
        simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
          Matrix.cons_val_one, negT_snd, e₁]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow, ofMul_one]
        module)
    have v : ∀ r : (T ⊗ A).left ⟶ (T ⊗ A).left,
        (nval ν r y J * nval ν (r ≫ (negT A T).left) y J).val = gs (r ≫ (fst T A).left) y ⊤ a := fun r =>
      (congrArg Units.val ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _)))).symm.trans (ha _ r y J hJ)
    have e : nval ν (𝟙 _) y J * nval ν (𝟙 _ ≫ (negT A T).left) y J = nval ν (𝟙 _ ≫ (translT A θ.pt).left) y J *
        nval ν ((𝟙 _ ≫ (translT A θ.pt).left) ≫ (negT A T).left) y J :=
      Units.ext (by rw [v, v, Category.assoc, translT_fst])
    rw [tval_conj _ _ _ _ _ hJ, tval_conj _ _ _ _ _ hJ, pt_conj, inv_inv]
    simp only [Category.assoc, negT_negT, translT_negT, Category.comp_id] at e ⊢
    apply Additive.ofMul.injective
    replace e := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e ⊢
    linear_combination (norm := abel) e

end Conj

def delta (hs : L.IsSymmetric) (hp : Function.Surjective (fst T A).left.appTop.hom) :
    ThetaGrp A L.L k T ≃* ThetaGrp A L.L k T :=
  have h := (SymLiftConst.exists_gen_neg L hs k T).choose_spec
  { conj _ h with
    invFun := conj _ h
    left_inv := conj_conj _ h hp
    right_inv := conj_conj _ h hp }

section Delta

variable (hs : L.IsSymmetric) (hp : Function.Surjective (fst T A).left.appTop.hom)

theorem pt_delta (θ : ThetaGrp A L.L k T) : (delta hs hp θ).pt = θ.pt⁻¹ :=
  pt_conj _ (SymLiftConst.exists_gen_neg L hs k T).choose_spec θ

theorem delta_scalar (c : Γ(T.left, ⊤)ˣ) : delta hs hp (scalar k T L c) = scalar k T L c :=
  conj_scalar _ (SymLiftConst.exists_gen_neg L hs k T).choose_spec c

theorem delta_delta (θ : ThetaGrp A L.L k T) : delta hs hp (delta hs hp θ) = θ :=
  conj_conj _ (SymLiftConst.exists_gen_neg L hs k T).choose_spec hp θ

end Delta

theorem exists_lift (c : CubicalStr A L) {V : Type} [CommRing V] [IsLocalRing V] (t : Sp V ⟶ S) {n : ℕ}
    {x : Over.mk t ⟶ A} (hx : x ^ n = 1) : ∃ θ : ThetaGrp A L.L n (Over.mk t), θ.pt = x := by
  obtain ⟨v, hv⟩ := DVR.exists_gen_of_local (V := V) L.L L.isLB (K := Fin 2) ![(1 : Over.mk t ⟶ A).left, x.left]
    ![(n : ℤ), -(n : ℤ)]
  exact exists_theta c hx v hv fun U _ h => Fin.prod_univ_two _

end Group

section EndPull

variable [IsCommMonObj A] {L : RigLB A} {φ : A ⟶ A} {a b : ℤ}
  (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) (h₀ : α₀.IsGen) (T : Over S)

def endPull : SecM A L.L b T →ₗ[Γ(T.left, ⊤)] SecM A L.L a T :=
  twist L.isLB (ψ := PullbackSections.endT A T φ) (lift_snd _ _) (lift_fst _ _) _
    (TransPullCompare.exists_pull_gen L.isLB α₀ h₀ T).choose_spec.1

variable {T}

end EndPull

end GlobalTheory.ThetaLaw
