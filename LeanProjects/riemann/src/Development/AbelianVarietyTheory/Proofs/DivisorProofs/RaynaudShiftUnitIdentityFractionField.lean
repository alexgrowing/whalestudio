import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR

set_option autoImplicit false

namespace GlobalTheory.ShiftUnit

theorem cv_nsmul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T : Over (Spec (CommRingCat.of R))}
    (g : GtPt D T) {y : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L y J) (a mu : D.X) (k : ℕ) :
    GlobalTheory.TorusModel.cv g (a + k • mu) y J * cubN (th D y J) k (cP D T a) (cP D T mu) g.b =
      GlobalTheory.TorusModel.cv g a y J * GlobalTheory.TorusModel.cv g mu y J ^ k := by
  induction k with
  | zero => rw [zero_nsmul, add_zero, pow_zero]; rfl
  | succ k ih =>
    have e := GlobalTheory.TorusModel.cv_add g hJ (a + k • mu) mu
    rw [cPoint_add, cPoint_nsmul] at e
    rw [succ_nsmul, ← add_assoc, cubN, Finset.prod_range_succ, mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, e, pow_succ,
      ← _root_.mul_assoc, ← ih, cubN, mul_right_comm]

theorem cst_mul {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of V)) (z : Z) (a b : V) :
    cst q z (a * b) = cst q z a * cst q z b := by
  unfold cst; rw [map_mul]; exact gs_mul q z ⊤ trivial _ _

theorem cst_pow {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of V)) (z : Z) (a : V) (n : ℕ) :
    cst q z (a ^ n) = cst q z a ^ n := by
  induction n with
  | zero => unfold cst; rw [pow_zero, pow_zero, map_one, gs_eq q z ⊤ trivial, map_one, map_one]
  | succ n ih => rw [pow_succ, cst_mul, ih, pow_succ]

end GlobalTheory.ShiftUnit

open GlobalTheory.ShiftUnit in

theorem GlobalTheory.ShiftUnit.shift_unit_identity : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), Q.TauBimult → ∀ (k : ℕ) (mu α : Q.X) (xp : 𝟙_ (Over (Sp R)) ⟶ Y.H) (A₀ B₀ P₀ : R) (ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c mu).left) fun _ => -1)) (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ xp⁻¹)).left ≫ Y.q.left] ![1, -1])), xp ≫ Y.q = Q.c mu → (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → cst (g ≫ jK R) z A₀ * (val ((Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ xp)).s α) (𝟙 Z) z J).val = cst (g ≫ jK R) z B₀ * (val (Q.tau mu α) g z J).val) → (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → (val (Q.psi mu) g z J).val = cst (g ≫ jK R) z P₀ * (val ψ₀ (g ≫ jK R) z J).val) → (∀ (T : Over (Sp R)) (y : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → val e y.left z J * val ψ₀ T.hom z J * val Q.rig T.hom z J * val ((Y.Φ T (y * (toUnit T ≫ xp⁻¹))).s mu) (𝟙 _) z J = 1) → ∀ (u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) k α mu) (DegPre.deltaε k))), u.IsGen → LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left) (DegPre.famMult Q (FractionRing R) k mu α) → ∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (pp : Over.mk (g ≫ jK R) ⟶ DegPre.BF Q (FractionRing R)) (yp : Over.mk (g ≫ jK R) ⟶ Y.H), (pp ≫ fst _ _).left ≫ jFK (R := R) (FractionRing R) = g → pp ≫ DegPre.prB Q (FractionRing R) = yp ≫ Y.q → ∀ (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → cst (g ≫ jK R) z B₀ * (val u (show Z ⟶ _ from pp.left) z J).val * (val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 Z) z J).val * ((val e (show Z ⟶ Y.H.left from (yp * (toUnit _ ≫ xp)).left) z J) ^ k).val = cst (g ≫ jK R) z (P₀ ^ k * A₀) * (val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 Z) z J).val := by
  intro R _ _ Q O _ _ _ oa Y hB k mu α xp A₀ B₀ P₀ ψ₀ e hxp hA hP he u hu hcorr Z g pp yp hg hpp z J hJ
  have e1 := (gen_fe (D := Q) (F := FractionRing R) GlobalTheory.SemiRigid.globalFns k mu α).2 u hu hcorr _ pp z J hJ
  rw [uVal, val_famMult _ hJ, hg, TWM.val_powGen, TWM.val_powGen] at e1
  have c1 : pp ≫ fst (TF (FractionRing R)) Q.P.A ≫ cP Q (TF (FractionRing R)) mu = cP Q (Over.mk (g ≫ jK R)) mu := by
    rw [← Category.assoc, comp_cP]
  have jr : (toUnit (TK R)).left = jK R := by simpa using Over.w (toUnit (TK R))
  have hr : val (Z := (Over.mk (g ≫ jK R)).left) Q.rigK g z J = val (Z := (Over.mk (g ≫ jK R)).left) Q.rig (g ≫ jK R) z J := by
    rw [DegPre.rigK, val_pull hJ, jr]
  rw [c1, hpp, hr] at e1
  have b1 : (Y.Φ (Over.mk (g ≫ jK R)) yp).b = yp ≫ Y.q := Ray.Φ_b Y yp
  have b2 : (Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ xp)).b = cP Q (Over.mk (g ≫ jK R)) mu := by
    rw [Ray.Φ_b, Category.assoc, hxp]; rfl
  have e2 : val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 _) z J *
      cubN (th Q z J) k (cP Q (Over.mk (g ≫ jK R)) α) (cP Q (Over.mk (g ≫ jK R)) mu) (yp ≫ Y.q) =
      val ((Y.Φ _ yp).s α) (𝟙 _) z J * val ((Y.Φ _ yp).s mu) (𝟙 _) z J ^ k := by
    have := cv_nsmul (Y.Φ _ yp) hJ α mu k
    rw [b1] at this
    exact this
  have e3 : val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 _) z J *
      th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu) =
      val ((Y.Φ _ yp).s α) (𝟙 _) z J * val ((Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ xp)).s α) (𝟙 _) z J := by
    have := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ yp (toUnit _ ≫ xp))).2 α z J hJ
    rw [b1, b2] at this
    exact this
  have m1 : (yp * (toUnit (Over.mk (g ≫ jK R)) ≫ xp)) * (toUnit (Over.mk (g ≫ jK R)) ≫ xp⁻¹) = yp := by
    rw [GrpObj.comp_inv, mul_inv_cancel_right]
  have e4 : val (Z := (Over.mk (g ≫ jK R)).left) e (yp * (toUnit _ ≫ xp)).left z J * val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J * val (Z := (Over.mk (g ≫ jK R)).left) Q.rig (g ≫ jK R) z J *
      val ((Y.Φ _ yp).s mu) (𝟙 _) z J = 1 := by
    have := he (Over.mk (g ≫ jK R)) (yp * (toUnit _ ≫ xp)) z J hJ
    rw [m1] at this
    exact this
  have e5 : (val (Z := (Over.mk (g ≫ jK R)).left) (Q.psi mu) g z J).val = cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z P₀ * (val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val :=
    hP Z g z J hJ
  have e6 : cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z A₀ * (val ((Y.Φ _ (toUnit _ ≫ xp)).s α) (𝟙 _) z J).val =
      cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z B₀ * (val (Z := (Over.mk (g ≫ jK R)).left) (Q.tau mu α) g z J).val :=
    hA Z g z J hJ
  have V : val (Z := (Over.mk (g ≫ jK R)).left) u pp.left z J * val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 _) z J * val (Z := (Over.mk (g ≫ jK R)).left) e (yp * (toUnit _ ≫ xp)).left z J ^ k *
      val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J ^ k =
      (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu))⁻¹ *
        val (Z := (Over.mk (g ≫ jK R)).left) (Q.tau mu α) g z J * val (Z := (Over.mk (g ≫ jK R)).left) (Q.psi mu) g z J ^ k * val ((Y.Φ _ yp).s α) (𝟙 _) z J := by
    apply Additive.ofMul.injective
    have a1 := congrArg Additive.ofMul e1
    have a2 := congrArg Additive.ofMul e2
    have a4 := congrArg Additive.ofMul e4
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at a1 a2 a4 ⊢
    have a4k := congrArg (k • ·) a4
    simp only [smul_add, smul_zero] at a4k
    linear_combination (norm := abel) a1 + a2 + a4k
  have Vv := congrArg Units.val V
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at Vv
  rw [e5, mul_pow] at Vv
  have e3v := congrArg Units.val e3
  simp only [Units.val_mul] at e3v
  have hθ : Units.val (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu)) * (Units.val (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu))⁻¹) = 1 := Units.mul_inv _
  suffices FINAL : cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z B₀ * (val (Z := (Over.mk (g ≫ jK R)).left) u pp.left z J).val * (val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 _) z J).val *
      ((val (Z := (Over.mk (g ≫ jK R)).left) e (yp * (toUnit _ ≫ xp)).left z J) ^ k).val =
    cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z (P₀ ^ k * A₀) * (val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 _) z J).val by exact FINAL
  rw [cst_mul, cst_pow, Units.val_pow_eq_pow_val]
  have hu0 : IsUnit ((val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val ^ k) := (Units.isUnit _).pow k
  apply hu0.mul_right_cancel
  linear_combination cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z B₀ * Vv + cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z P₀ ^ k * (val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val ^ k * cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z A₀ * (val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 _) z J).val * hθ - cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z P₀ ^ k * (val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val ^ k * cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z A₀ * (Units.val (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu))⁻¹) * e3v - cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z P₀ ^ k * (val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val ^ k * (val ((Y.Φ _ yp).s α) (𝟙 _) z J).val * (Units.val (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu))⁻¹) * e6
