import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsHomDivMulRefine

noncomputable section

namespace GlobalTheory.TauTwist

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorusExt

section Forms

variable (O : Type) [CommRing O] [StarRing O] {X : Type} [AddCommGroup X] [Module O X] {U U' : Type} [CommGroup U]
  [CommGroup U']

structure IsScalarForm (t : X → X → U) : Prop where
  add_right : ∀ y x x', t y (x + x') = t y x * t y x'
  symm : ∀ y x, t y x = t x y
  bal : ∀ (a : O) y x, t (a • y) x = t y (star a • x)

variable {O}

namespace IsScalarForm

variable {t s : X → X → U} (ht : IsScalarForm O t)
include ht

theorem add_left (y y' x : X) : t (y + y') x = t y x * t y' x := by
  rw [ht.symm, ht.add_right, ht.symm x, ht.symm x]

theorem zero_right (y : X) : t y 0 = 1 := by
  have := ht.add_right y 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem neg_right (y x : X) : t y (-x) = (t y x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← ht.add_right, neg_add_cancel, ht.zero_right]

theorem neg_left (y x : X) : t (-y) x = (t y x)⁻¹ := by rw [ht.symm, ht.neg_right, ht.symm]

theorem nsmul_right (n : ℕ) (y x : X) : t y (n • x) = t y x ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, ht.zero_right]
  | succ n ih => rw [succ_nsmul, pow_succ, ht.add_right, ih]

theorem nsmul_left (n : ℕ) (y x : X) : t (n • y) x = t y x ^ n := by rw [ht.symm, ht.nsmul_right, ht.symm]

theorem map (f : U →* U') : IsScalarForm O fun y x => f (t y x) :=
  ⟨fun y x x' => by rw [ht.add_right, map_mul], fun y x => by rw [ht.symm], fun a y x => by rw [ht.bal]⟩

theorem inv : IsScalarForm O fun y x => (t y x)⁻¹ := ht.map invMonoidHom

theorem pow (n : ℕ) : IsScalarForm O fun y x => t y x ^ n := ht.map (powMonoidHom n)

theorem mul (hs : IsScalarForm O s) : IsScalarForm O fun y x => t y x * s y x :=
  ⟨fun y x x' => by rw [ht.add_right, hs.add_right, _root_.mul_mul_mul_comm], fun y x => by rw [ht.symm, hs.symm],
    fun a y x => by rw [ht.bal, hs.bal]⟩

theorem mem_balForms : Forms.bilOfMul t ht.add_left ht.add_right ∈ Forms.balForms ℤ O X (Additive U) :=
  ⟨ht.symm, ht.bal⟩

theorem refine_add {w : O} (hw : w + star w = 1) (a b : X) :
    t (a + b) (w • (a + b)) = t a (w • a) * t b (w • b) * t a b := by
  have h : t a (w • b) * t b (w • a) = t a b := by
    rw [ht.symm b, ht.bal, ← ht.add_right, ← add_smul, hw, one_smul]
  rw [smul_add, ht.add_left, ht.add_right, ht.add_right, ← h]
  ac_rfl

theorem refine_neg (w : O) (a : X) : t (-a) (w • -a) = t a (w • a) := by
  rw [smul_neg, ht.neg_left, ht.neg_right, inv_inv]

end IsScalarForm

end Forms

section Constants

variable {A A' : Type} [CommRing A] [CommRing A'] {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K]
  [Fintype K']

def unitAt (q : Z ⟶ Sp A) (z : Z) : Aˣ →* (Z.presheaf.stalk z)ˣ :=
  (gm q z ⊤).comp (Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom)

theorem unitAt_apply (q : Z ⟶ Sp A) (z : Z) (u : Aˣ) : unitAt q z u = gm q z ⊤ (unitOn u) := rfl

theorem unitAt_val (q : Z ⟶ Sp A) (z : Z) (u : Aˣ) : (unitAt q z u).val = gs q z ⊤ (unitOn u).val :=
  (gs_unit q z ⊤ trivial (unitOn u)).symm

theorem unitAt_spMap (q : Z ⟶ Sp A') (f : A →+* A') (z : Z) (u : Aˣ) :
    unitAt (q ≫ spMap f) z u = unitAt q z (Units.map f.toMonoidHom u) := by
  refine (gm_pull q (spMap f) z ⊤ trivial (unitOn u)).symm.trans (congrArg (gm q z ⊤) (Units.ext ?_))
  exact (congrArg (fun e => e.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

theorem unitAt_injective {F : Type} [Field F] (y : Sp F) : Function.Injective (unitAt (𝟙 (Sp F)) y) :=
  fun u v h => (stalkUnits y).injective ((gm_unitOn y u).symm.trans (h.trans (gm_unitOn y v)))

theorem val_scale {φ : K → (Sp A ⟶ X)} {ε : K → ℤ} (u : Aˣ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Sp A) {z : Z}
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) : val (scaleGen (unitOn u) t) r z J = unitAt r z u * val t r z J :=
  val_scaleGen _ t r hJ

theorem val_powGen {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ X) → L.ι) : val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n := map_pow _ _ _

end Constants

variable {R : Type} [CommRing R] [IsDomain R]

abbrev PsiFam (D : DegPre R) : Type :=
  ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptK (D.c χ)) (fun _ => -1))

@[reducible] def withPsi (D : DegPre R) (ψ : PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen) : DegPre R :=
  { D with psi := ψ, psi_gen := hψ }

@[reducible] def rescale (D : DegPre R) (q : D.X → (FractionRing R)ˣ) : DegPre R :=
  withPsi D (fun χ => scaleGen (unitOn (q χ)) (D.psi χ)) fun χ => scaleGen_isGen _ _ (D.psi_gen χ)

variable {O : Type} [CommRing O] [StarRing O]

@[reducible] def twist (D : DegPre R) [Module O D.X] (w : O) (t : D.X → D.X → (FractionRing R)ˣ) : DegPre R :=
  rescale D fun y => t y (w • y)

variable {D : DegPre R}

theorem val_tau (D : DegPre R) (a b : D.X) {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J} (hJ : Good D.P.L z J) :
    val (D.tau a b) r z J = val (D.psi (a + b)) r z J * (val (D.psi a) r z J)⁻¹ * (val (D.psi b) r z J)⁻¹ *
      (val D.rigK r z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem val_psi_rescale (q : D.X → (FractionRing R)ˣ) (a : D.X) {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J}
    (hJ : Good D.P.L z J) : val ((rescale D q).psi a) r z J = unitAt r z (q a) * val (D.psi a) r z J :=
  val_scale (q a) (D.psi a) r hJ

theorem val_tau_rescale (q : D.X → (FractionRing R)ˣ) {a b : D.X} {x : (FractionRing R)ˣ}
    (hx : q (a + b) = q a * q b * x) {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J} (hJ : Good D.P.L z J) :
    val ((rescale D q).tau a b) r z J = unitAt r z x * val (D.tau a b) r z J := by
  have e := val_tau (rescale D q) a b r hJ
  have e₁ := val_psi_rescale q (a + b) r hJ
  have e₂ := val_psi_rescale q a r hJ
  have e₃ := val_psi_rescale q b r hJ
  have e₄ := val_tau D a b r hJ
  rw [hx, map_mul, map_mul] at e₁
  have e₅ : val (rescale D q).rigK r z J = val D.rigK r z J := rfl
  rw [e₁, e₂, e₃, e₅] at e
  rw [e, e₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem psiUnitOn_rescale (q : D.X → (FractionRing R)ˣ) {χ : D.X} (u : Rˣ)
    (hu : q χ = Units.map (algebraMap R (FractionRing R)).toMonoidHom u) {U : Set (Sp R)} (h : PsiUnitOn D χ U) :
    PsiUnitOn (rescale D q) χ U := by
  intro j V hV hU hc hle
  obtain ⟨r, hr, e⟩ := h j V hV hU hc hle
  refine ⟨(res (le_top : V ≤ ⊤) (unitOn u)).val * r, (Units.isUnit _).mul hr, ?_⟩
  rw [map_mul, e]
  refine Eq.trans (congrArg₂ (· * ·) ?_ rfl) (map_mul _ (res le_top (unitOn (q χ))).val ((D.psi χ).s j).val).symm
  refine fn_ext fun y hy => ?_
  refine (gs_pull (𝟙 _) (jK R) y V hy _).trans ((gs_unit _ y V hy _).trans (Eq.trans ?_
    ((gs_res (𝟙 _) y hle hy _).trans (gs_unit _ y _ (hle hy) _)).symm))
  refine congrArg Units.val ((gm_res _ y le_top hy _).trans (Eq.trans ?_ (gm_res _ y le_top (hle hy) _).symm))
  rw [hu]
  exact unitAt_spMap (𝟙 _) (algebraMap R (FractionRing R)) y u

section Twist

variable [Module O D.X] {w : O} {t : D.X → D.X → (FractionRing R)ˣ}

theorem val_psi_twist (w : O) (t : D.X → D.X → (FractionRing R)ˣ) (a : D.X) {Z : Scheme.{0}} (r : Z ⟶ (TK R).left)
    {z : Z} {J} (hJ : Good D.P.L z J) :
    val ((twist D w t).psi a) r z J = unitAt r z (t a (w • a)) * val (D.psi a) r z J :=
  val_psi_rescale (fun y => t y (w • y)) a r hJ

variable (hw : w + star w = 1) (ht : IsScalarForm O t)
include ht

theorem psiEven_twist (w : O) (h : D.PsiEven) : (twist D w t).PsiEven := fun χ =>
  corr_of_val D.P.isLB fun y J hJ => by
    have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (h χ) (𝟙 _))
    refine (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_psi_twist w t (-χ) _ hJ) rfl).trans
      (Eq.trans ?_ (val_psi_twist w t χ _ hJ).symm))
    rw [ht.refine_neg, ← e, _root_.mul_assoc]

include hw

theorem val_tau_twist (a b : D.X) {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J} (hJ : Good D.P.L z J) :
    val ((twist D w t).tau a b) r z J = unitAt r z (t a b) * val (D.tau a b) r z J :=
  val_tau_rescale (fun y => t y (w • y)) (ht.refine_add hw a b) r hJ

theorem tauBimult_twist (h : D.TauBimult) : (twist D w t).TauBimult := fun a a' b =>
  corr_of_val D.P.isLB fun y J hJ => by
    have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
    refine (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_tau_twist hw ht (a + a') b _ hJ) rfl).trans
      (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_tau_twist hw ht a b _ hJ)
        (val_tau_twist hw ht a' b _ hJ))).symm))
    rw [ht.add_left, map_mul, _root_.mul_mul_mul_comm, ← e, _root_.mul_assoc]
    rfl

def twistAct (oa : D.OAct O) : (twist D w t).OAct O where
  onB := oa.onB
  c_lin := oa.c_lin
  tau_bal a u hu u₀ x x' := corr_of_val D.P.isLB fun y J hJ => by
    have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (oa.tau_bal a u hu u₀ x x') (𝟙 _))
    refine (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_tau_twist hw ht (a • x) x' _ hJ) rfl).trans
      (Eq.trans ?_ (val_tau_twist hw ht x (star a • x') _ hJ).symm))
    rw [ht.bal, ← e, _root_.mul_assoc]
    rfl

theorem psi_weight_zero_twist {oa : D.OAct O} (h : TraceFormTwistIso D oa w) : TraceFormTwistIso (twist D w t) (twistAct hw ht oa) w := by
  obtain ⟨u, hu, u₀, h⟩ := h
  refine ⟨u, hu, u₀, fun x => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h x) (𝟙 _)).trans (val_mul hJ _ _ _))
  refine (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_tau_twist hw ht x (w • x) _ hJ) rfl).trans
    (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_psi_twist w t x _ hJ) rfl)).symm))
  rw [_root_.mul_assoc, _root_.mul_assoc]
  exact congrArg _ e

omit hw ht in
theorem psiUnitOn_twist (w : O) (t₀ : D.X → D.X → Rˣ) {χ : D.X} {U : Set (Sp R)} (h : PsiUnitOn D χ U) :
    PsiUnitOn (twist D w fun y x => Units.map (algebraMap R (FractionRing R)).toMonoidHom (t₀ y x)) χ U :=
  psiUnitOn_rescale _ (t₀ χ (w • χ)) rfl h

end Twist

end GlobalTheory.TauTwist
