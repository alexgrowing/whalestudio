import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocallyNoetherian
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymLiftMul

section Alg

variable {G U : Type} [CommGroup G] [CommGroup U] {a b : G} {fa fb fc ν : G → U} {ρ ε : U}

theorem sq_factor (hm : ∀ y, fa y * fb (a * y) = ρ * fc y) (hc : ∀ y, fa y * fb (a * y) = fb y * fa (b * y) * ε)
    (sa : ∀ y, fa (a⁻¹ * y) * ν y * (fa y⁻¹ * (ν (a⁻¹ * y))⁻¹) = 1)
    (sb : ∀ y, fb (b⁻¹ * y) * ν y * (fb y⁻¹ * (ν (b⁻¹ * y))⁻¹) = 1)
    (sc : ∀ y, fc ((a * b)⁻¹ * y) * ν y * (fc y⁻¹ * (ν ((a * b)⁻¹ * y))⁻¹) = 1) : ρ ^ 2 = ε := by
  have e1 : a * (a * b)⁻¹ = b⁻¹ := by rw [mul_inv, mul_inv_cancel_left]
  have e2 : b * (a * b)⁻¹ = a⁻¹ := by rw [mul_inv, mul_left_comm, mul_inv_cancel, _root_.mul_one]
  have e3 : b⁻¹ * a⁻¹ = (a * b)⁻¹ := by rw [mul_inv, mul_comm]
  have E1 := hm (a * b)⁻¹
  have E2 := hm 1
  have E3 := sc 1
  have E4 := hc (a * b)⁻¹
  have E5 := sa 1
  have E6 := sb a⁻¹
  rw [e1] at E1 E4
  rw [e2] at E4
  rw [_root_.mul_one] at E2 E3 E5
  rw [inv_one] at E3 E5
  rw [e3, inv_inv] at E6
  calc ρ ^ 2 = ρ ^ 2 * (fc (a * b)⁻¹ * ν 1 * (fc 1 * (ν (a * b)⁻¹)⁻¹)) := by rw [E3, _root_.mul_one]
    _ = (ρ * fc (a * b)⁻¹) * (ρ * fc 1) * ν 1 * (ν (a * b)⁻¹)⁻¹ := by rw [sq]; ac_rfl
    _ = (fb (a * b)⁻¹ * fa a⁻¹ * ε) * (fa 1 * fb a) * ν 1 * (ν (a * b)⁻¹)⁻¹ := by rw [← E1, ← E2, E4]
    _ = ε * (fa a⁻¹ * ν 1 * fa 1) * (fb (a * b)⁻¹ * fb a * (ν (a * b)⁻¹)⁻¹) * ((ν a⁻¹)⁻¹ * ν a⁻¹) := by
        rw [inv_mul_cancel, _root_.mul_one]; ac_rfl
    _ = ε * (fa a⁻¹ * ν 1 * (fa 1 * (ν a⁻¹)⁻¹)) * (fb (a * b)⁻¹ * ν a⁻¹ * (fb a * (ν (a * b)⁻¹)⁻¹)) := by ac_rfl
    _ = ε := by rw [E5, E6, _root_.mul_one, _root_.mul_one]

theorem comm_pow (hc : ∀ y, fa y * fb (a * y) = fb y * fa (b * y) * ε) (m : ℕ) (y : G) :
    fa y * ∏ j ∈ Finset.range m, fb (b ^ j * (a * y)) =
      ε ^ m * (∏ j ∈ Finset.range m, fb (b ^ j * y)) * fa (b ^ m * y) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ← _root_.mul_assoc (fa y), ih]
    have e1 : b ^ m * (a * y) = a * (b ^ m * y) := mul_left_comm _ _ _
    have e2 : b ^ (m + 1) * y = b * (b ^ m * y) := by rw [pow_succ', _root_.mul_assoc]
    rw [e1, e2, pow_succ, _root_.mul_assoc (ε ^ m * _), hc (b ^ m * y)]
    ac_rfl

theorem prod_pow (hm : ∀ y, fa y * fb (a * y) = ρ * fc y) (hc : ∀ y, fa y * fb (a * y) = fb y * fa (b * y) * ρ ^ 2)
    (m : ℕ) (y : G) : ρ ^ (m * m) * ∏ j ∈ Finset.range m, fc ((a * b) ^ j * y) =
      (∏ j ∈ Finset.range m, fa (a ^ j * y)) * ∏ j ∈ Finset.range m, fb (b ^ j * (a ^ m * y)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have key := comm_pow hc m (a ^ m * y)
    have h1 := hm (b ^ m * (a ^ m * y))
    have e1 : (a * b) ^ m * y = b ^ m * (a ^ m * y) := by rw [mul_pow]; ac_rfl
    have e2 : a * (b ^ m * (a ^ m * y)) = b ^ m * (a ^ (m + 1) * y) := by rw [pow_succ]; ac_rfl
    have e3 : a * (a ^ m * y) = a ^ (m + 1) * y := by rw [pow_succ]; ac_rfl
    have ep : ρ ^ ((m + 1) * (m + 1)) = ρ ^ (m * m) * (ρ ^ 2) ^ m * ρ := by
      rw [← pow_mul, ← pow_add, ← pow_succ]; congr 1; ring
    rw [e2] at h1
    rw [e3] at key
    simp only [Finset.prod_range_succ]
    rw [e1, ep]
    calc ρ ^ (m * m) * (ρ ^ 2) ^ m * ρ * ((∏ j ∈ Finset.range m, fc ((a * b) ^ j * y)) * fc (b ^ m * (a ^ m * y)))
        = (ρ ^ (m * m) * ∏ j ∈ Finset.range m, fc ((a * b) ^ j * y)) * (ρ ^ 2) ^ m *
            (ρ * fc (b ^ m * (a ^ m * y))) := by ac_rfl
      _ = (∏ j ∈ Finset.range m, fa (a ^ j * y)) * (∏ j ∈ Finset.range m, fb (b ^ j * (a ^ m * y))) * (ρ ^ 2) ^ m *
            (fa (b ^ m * (a ^ m * y)) * fb (b ^ m * (a ^ (m + 1) * y))) := by rw [ih, ← h1]
      _ = (∏ j ∈ Finset.range m, fa (a ^ j * y)) * ((ρ ^ 2) ^ m * (∏ j ∈ Finset.range m, fb (b ^ j * (a ^ m * y))) *
            fa (b ^ m * (a ^ m * y))) * fb (b ^ m * (a ^ (m + 1) * y)) := by ac_rfl
      _ = (∏ j ∈ Finset.range m, fa (a ^ j * y)) * fa (a ^ m * y) *
            ((∏ j ∈ Finset.range m, fb (b ^ j * (a ^ (m + 1) * y))) * fb (b ^ m * (a ^ (m + 1) * y))) := by
          rw [← key]; ac_rfl

theorem pow_factor {n : ℕ} (hn : Odd n) (hm : ∀ y, fa y * fb (a * y) = ρ * fc y)
    (hc : ∀ y, fa y * fb (a * y) = fb y * fa (b * y) * ρ ^ 2)
    (pa : ∀ y, ∏ j ∈ Finset.range n, fa (a ^ j * y) = 1) (pb : ∀ y, ∏ j ∈ Finset.range n, fb (b ^ j * y) = 1)
    (pc : ∀ y, ∏ j ∈ Finset.range n, fc ((a * b) ^ j * y) = 1) (hp : fa (b ^ n * 1) = fa 1) : ρ ^ n = 1 := by
  obtain ⟨k, hk⟩ := hn
  have h1 : ρ ^ (n * n) = 1 := by
    have := prod_pow hm hc n 1
    rw [pc 1, pa 1, pb (a ^ n * 1), _root_.mul_one, _root_.mul_one] at this
    exact this
  have h2 : (ρ ^ 2) ^ n = 1 := by
    have := comm_pow hc n 1
    rw [pb (a * 1), pb 1, hp, _root_.mul_one, _root_.mul_one] at this
    exact mul_right_cancel (this.symm.trans (_root_.one_mul _).symm)
  have h3 : ρ ^ (n * n) = ((ρ ^ 2) ^ n) ^ k * ρ ^ n := by
    rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; rw [hk]; ring
  rw [h1, h2, one_pow, _root_.one_mul] at h3
  exact h3.symm

end Alg

open GlobalTheory.CommPairing GlobalTheory.ThetaAct GlobalTheory.GlobalLift

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T T' : Over S}

theorem lift_translT (σ : T' ⟶ T) (y : T' ⟶ A) (x : T ⟶ A) :
    (lift σ y).left ≫ (translT A x).left = (lift σ ((σ ≫ x) * y)).left := by
  rw [← Over.comp_left, GlobalTheory.CommutatorPairing.lift_translT]

theorem lift_negT (σ : T' ⟶ T) (y : T' ⟶ A) : (lift σ y).left ≫ (negT A T).left = (lift σ y⁻¹).left := by
  have e : y ≫ GrpObj.inv = y⁻¹ := rfl
  unfold negT
  rw [← Over.comp_left, CartesianMonoidalCategory.comp_lift, CartesianMonoidalCategory.lift_fst,
    CartesianMonoidalCategory.lift_snd_assoc, e]

omit [GrpObj A] in
theorem lift_fst_left (σ : T' ⟶ T) (y : T' ⟶ A) : (lift σ y).left ≫ (fst T A).left = σ.left := by
  rw [← Over.comp_left, CartesianMonoidalCategory.lift_fst]

private theorem comp_pow_cusp_form_evaluations {X Y : Over S} (f : X ⟶ Y) (x : Y ⟶ A) (m : ℕ) : f ≫ x ^ m = (f ≫ x) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ m ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem pow_val {θ : ThetaGrp A L k T} {n : ℕ} (h : LB.Gen.Corr L _ _ _ _ (powGen A L k θ n) (LB.oneGen L))
    (σ : T' ⟶ T) {z : T'.left} {J} (hJ : Good L z J) (y : T' ⟶ A) :
    ∏ j ∈ Finset.range n, tval θ (lift σ ((σ ≫ θ.pt) ^ j * y)).left z J = 1 := by
  have h1 := val_corr hJ h (lift σ y).left
  rw [val_powGen θ n _ hJ, val_one] at h1
  refine Eq.trans ?_ h1
  rw [Finset.prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [lift_translT, comp_pow_cusp_form_evaluations]

private theorem exp_le_qw_div_le_exp_of_far_letters {U : Type} [CommGroup U] (t1 t2 a a' b b' : U) (hv : t1 * b * (t2 * b'⁻¹) = 1)
    (hd : a * b⁻¹ = a' * b'⁻¹) : t1 * a * (t2 * a'⁻¹) = 1 := by
  calc t1 * a * (t2 * a'⁻¹) = t1 * a * (t2 * a'⁻¹) * (b * b⁻¹) * (b'⁻¹ * b') := by
        rw [_root_.mul_inv_cancel, _root_.inv_mul_cancel, _root_.mul_one, _root_.mul_one]
    _ = t1 * b * (t2 * b'⁻¹) * (a * b⁻¹) * (b' * a'⁻¹) := by ac_rfl
    _ = t1 * b * (t2 * b'⁻¹) * (a * b⁻¹) * (a' * b'⁻¹)⁻¹ := by rw [_root_.mul_inv_rev, inv_inv]
    _ = 1 := by rw [hv, _root_.one_mul, hd, _root_.mul_inv_cancel]

private theorem comp_inv_cusp_form_evaluations {X Y : Over S} (f : X ⟶ Y) (x : Y ⟶ A) : f ≫ x⁻¹ = (f ≫ x)⁻¹ := by
  show f ≫ (x ≫ GrpObj.inv) = (f ≫ x) ≫ GrpObj.inv
  rw [Category.assoc]

theorem sym_val' (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {θ : ThetaGrp A L k T} {n : ℕ} {x : T ⟶ A}
    (h : SymLift A L k n x θ) {ν : LB.Gen (negLB A L k T)} (hν : ν.IsGen) (σ : T' ⟶ T) {z : T'.left} {J}
    (hJ : Good L z J) (y : T' ⟶ A) :
    tval θ (lift σ ((σ ≫ x)⁻¹ * y)).left z J * nval ν (lift σ y).left z J *
      (tval θ (lift σ y⁻¹).left z J * (nval ν (lift σ ((σ ≫ x)⁻¹ * y)).left z J)⁻¹) = 1 := by
  obtain ⟨hpt, -, nu, hnu, hsym⟩ := h
  have hv := val_corr hJ hsym (lift σ y).left
  rw [val_symGen θ nu _ hJ, val_one] at hv
  have hd : nval ν (lift σ y).left z J * (nval nu (lift σ y).left z J)⁻¹ =
      nval ν ((lift σ y).left ≫ (translT A θ.pt⁻¹).left) z J *
        (nval nu ((lift σ y).left ≫ (translT A θ.pt⁻¹).left) z J)⁻¹ :=
    GlobalTheory.CommPairing.val_div_eq hL (fst T A).left (GlobalTheory.CommPairing.surj_fst hG hA T) hν hnu _ _
      (by rw [Category.assoc, GlobalTheory.CommPairing.translT_fst]) z J hJ
  rw [lift_translT, lift_negT, comp_inv_cusp_form_evaluations, hpt] at hv
  rw [lift_translT, comp_inv_cusp_form_evaluations, hpt] at hd
  exact exp_le_qw_div_le_exp_of_far_letters _ _ _ _ _ _ hv hd

theorem tval_trans (θ : ThetaGrp A L k T) (σ : T' ⟶ T) {z : T'.left} {J J'} (hJ : Good L z J) (hJ' : Good L z J')
    (y : T' ⟶ A) : tval θ (lift σ y).left z J =
      gm y.left z (L.U (J y.left) ⊓ L.U (J' y.left)) (L.g _ _) ^ k *
        (gm ((σ ≫ θ.pt) * y).left z (L.U (J ((σ ≫ θ.pt) * y).left) ⊓ L.U (J' ((σ ≫ θ.pt) * y).left)) (L.g _ _) ^ k)⁻¹ *
        tval θ (lift σ y).left z J' := by
  have e0 : (lift σ y).left ≫ (snd T A).left = y.left := by
    rw [← Over.comp_left, CartesianMonoidalCategory.lift_snd]
  have e1 : (lift σ y).left ≫ (translPt A θ.pt).left = ((σ ≫ θ.pt) * y).left := by
    rw [← Over.comp_left, GlobalTheory.CommutatorPairing.lift_translPt]
  unfold tval val
  refine (gen_trans θ.isGen (lift σ y).left z (Good.mem hJ _ _) (Good.mem hJ' _ _)).trans ?_
  refine congrArg₂ (· * ·) ?_ rfl
  unfold trF
  rw [Fin.prod_univ_two, ← e0, ← e1, ← zpow_neg]
  rfl

private theorem prod_range_mul_inv_succ {U : Type} [CommGroup U] (f : ℕ → U) (n : ℕ) :
    ∏ i ∈ Finset.range n, f i * (f (i + 1))⁻¹ = f 0 * (f n)⁻¹ := by
  induction n with
  | zero => rw [Finset.prod_range_zero, _root_.mul_inv_cancel]
  | succ n ih => rw [Finset.prod_range_succ, ih, _root_.mul_assoc, inv_mul_cancel_left]

theorem trans_trivial (hL : L.IsLB) {θ : ThetaGrp A L k T} {n : ℕ}
    (h : LB.Gen.Corr L _ _ _ _ (powGen A L k θ n) (LB.oneGen L)) (hn : θ.pt ^ n ≠ 1) (y : T ⊗ A ⟶ A)
    (z : (T ⊗ A).left) {i i' : L.ι}
    (hi : y.left z ∈ L.U i) (hi' : y.left z ∈ L.U i') :
    gm y.left z (L.U i ⊓ L.U i') (L.g i i') ^ k = 1 := by
  classical
  let J0 : ((T ⊗ A).left ⟶ A.left) → L.ι := fun ψ => (exists_chart hL (ψ z)).choose
  have hJ0 : ∀ ψ, ψ z ∈ L.U (J0 ψ) := fun ψ => (exists_chart hL (ψ z)).choose_spec
  set J := Function.update J0 y.left i with hJeq
  set J' := Function.update J0 y.left i' with hJ'eq
  have hJy : J y.left = i := by simp [hJeq]
  have hJy' : J' y.left = i' := by simp [hJ'eq]
  have hJn : ∀ ψ, ψ ≠ y.left → J ψ = J' ψ := fun ψ hψ => by simp [hJeq, hJ'eq, hψ]
  have hJ : Good L z J := fun ψ => by
    by_cases hψ : ψ = y.left
    · rw [hψ, hJy]; exact hi
    · rw [hJeq, Function.update_of_ne hψ]; exact hJ0 ψ
  have hJ' : Good L z J' := fun ψ => by
    by_cases hψ : ψ = y.left
    · rw [hψ, hJy']; exact hi'
    · rw [hJ'eq, Function.update_of_ne hψ]; exact hJ0 ψ
  set r : (T ⊗ A).left ⟶ (T ⊗ A).left := (lift (fst T A) y).left with hr
  have v1 := val_corr hJ h r
  have v2 := val_corr hJ' h r
  rw [val_one, val_powGen θ n r hJ] at v1
  rw [val_one, val_powGen θ n r hJ'] at v2
  set G : ℕ → (((T ⊗ A).left).presheaf.stalk z)ˣ := fun m =>
    gm ((fst T A ≫ θ.pt ^ m) * y).left z (L.U (J ((fst T A ≫ θ.pt ^ m) * y).left) ⊓
      L.U (J' ((fst T A ≫ θ.pt ^ m) * y).left)) (L.g _ _) ^ k with hGe
  have et : ∀ m : ℕ, r ≫ (translT A (θ.pt ^ m)).left = (lift (fst T A) ((fst T A ≫ θ.pt ^ m) * y)).left :=
    fun m => by rw [hr, lift_translT]
  have em : ∀ m : ℕ, (fst T A ≫ θ.pt) * ((fst T A ≫ θ.pt ^ m) * y) = (fst T A ≫ θ.pt ^ (m + 1)) * y :=
    fun m => by rw [← _root_.mul_assoc, ← MonObj.comp_mul, pow_succ']
  have step : ∀ m : ℕ, tval θ (r ≫ (translT A (θ.pt ^ m)).left) z J =
      G m * (G (m + 1))⁻¹ * tval θ (r ≫ (translT A (θ.pt ^ m)).left) z J' := fun m => by
    rw [hGe, et, tval_trans θ (fst T A) hJ hJ' ((fst T A ≫ θ.pt ^ m) * y), em]
  have hprod : ∏ i ∈ Finset.range n, G i * (G (i + 1))⁻¹ = 1 := by
    rw [← Fin.prod_univ_eq_prod_range (fun m => G m * (G (m + 1))⁻¹) n]
    calc ∏ i : Fin n, G i * (G (i + 1))⁻¹
        = (∏ i : Fin n, G i * (G (i + 1))⁻¹) * ∏ i : Fin n, tval θ (r ≫ (translT A (θ.pt ^ (i : ℕ))).left) z J' := by
          rw [v2, _root_.mul_one]
      _ = ∏ i : Fin n, tval θ (r ≫ (translT A (θ.pt ^ (i : ℕ))).left) z J := by
          rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl fun i _ => (step i).symm
      _ = 1 := v1
  rw [prod_range_mul_inv_succ] at hprod
  have e00 : (fst T A ≫ θ.pt ^ 0) * y = y := by rw [pow_zero, MonObj.comp_one, _root_.one_mul]
  have q0 : G 0 = gm y.left z (L.U i ⊓ L.U i') (L.g i i') ^ k := by
    rw [hGe]; dsimp only; rw [e00, hJy, hJy']
  have qn : G n = 1 := by
    by_cases hq : ((fst T A ≫ θ.pt ^ n) * y).left = y.left
    · exfalso
      refine hn ?_
      have h2 : (fst T A ≫ θ.pt ^ n) * y = y := Over.OverMorphism.ext hq
      have h3 : fst T A ≫ θ.pt ^ n = 1 := mul_right_cancel (h2.trans (_root_.one_mul y).symm)
      have h4 := congrArg (fun w => lift (𝟙 T) (1 : T ⟶ A) ≫ w) h3
      simpa [MonObj.comp_one] using h4
    · rw [hGe]; dsimp only; rw [hJn _ hq, gm_self hL _ z (hJ' _), one_zpow]
  rw [q0, qn, inv_one, _root_.mul_one] at hprod
  exact hprod

theorem tval_periodic (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {θ : ThetaGrp A L k T} {n : ℕ}
    (h : LB.Gen.Corr L _ _ _ _ (powGen A L k θ n) (LB.oneGen L)) (ξ : ThetaGrp A L k T) (σ : T' ⟶ T) {z : T'.left} {J}
    (hJ : Good L z J) : tval ξ (lift σ ((σ ≫ θ.pt) ^ n * 1)).left z J = tval ξ (lift σ 1).left z J := by
  by_cases hn : θ.pt ^ n = 1
  · rw [← comp_pow_cusp_form_evaluations, hn, MonObj.comp_one, _root_.one_mul]
  · have htr := fun (y : T ⊗ A ⟶ A) (q : (T ⊗ A).left) (i i' : L.ι) (hi : y.left q ∈ L.U i)
        (hi' : y.left q ∈ L.U i') => trans_trivial hL h hn y q hi hi'
    have hcomp : ∀ (q : (T ⊗ A).left) (j j' : Fin 2 → L.ι),
        q ∈ LB.wchart L ![(snd T A).left, (translPt A ξ.pt).left] j →
        q ∈ LB.wchart L ![(snd T A).left, (translPt A ξ.pt).left] j' →
        trF ![(snd T A).left, (translPt A ξ.pt).left] ![k, -k] (𝟙 _) q j j' = 1 := by
      intro q j j' hj hj'
      have m0 : ∀ j, q ∈ LB.wchart L ![(snd T A).left, (translPt A ξ.pt).left] j → (snd T A).left q ∈ L.U (j 0) :=
        fun j hj => Set.mem_iInter.1 hj 0
      have m1 : ∀ j, q ∈ LB.wchart L ![(snd T A).left, (translPt A ξ.pt).left] j →
          (translPt A ξ.pt).left q ∈ L.U (j 1) := fun j hj => Set.mem_iInter.1 hj 1
      have a0 := htr (snd T A) q (j 0) (j' 0) (m0 j hj) (m0 j' hj')
      have a1 := htr (translPt A ξ.pt) q (j 1) (j' 1) (m1 j hj) (m1 j' hj')
      have ex : trF ![(snd T A).left, (translPt A ξ.pt).left] ![k, -k] (𝟙 _) q j j' =
          gm (snd T A).left q (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) ^ k *
            gm (translPt A ξ.pt).left q (L.U (j 1) ⊓ L.U (j' 1)) (L.g (j 1) (j' 1)) ^ (-k) := by
        unfold trF
        rw [Fin.prod_univ_two, Category.id_comp, Category.id_comp]
        rfl
      rw [ex, a0, zpow_neg, a1, inv_one, _root_.mul_one]
    obtain ⟨s, hs⟩ := glue_unit (X := (T ⊗ A).left) ⊤
      (fun j : Fin 2 → L.ι => LB.wchart L ![(snd T A).left, (translPt A ξ.pt).left] j) (fun _ => le_top)
      (by
        intro q _
        have hq : ∀ b : Fin 2, ∃ i, (![(snd T A).left, (translPt A ξ.pt).left] b) q ∈ L.U i :=
          fun b => exists_chart hL _
        choose j hj using hq
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, Set.mem_iInter.2 hj⟩)
      (fun j => ξ.φ.s j)
      (fun i j q hq => (gen_trans ξ.isGen (𝟙 _) q hq.1 hq.2).trans (by rw [hcomp q i j hq.1 hq.2, _root_.one_mul]))
    have hv : ∀ (r : T'.left ⟶ (T ⊗ A).left), tval ξ r z J = gm r z ⊤ s := fun r =>
      ((gm_res r z le_top (Good.mem hJ _ r) s).symm.trans (congrArg (gm r z _) (hs _))).symm
    obtain ⟨c0, hc0⟩ := GlobalTheory.CommPairing.surj_fst hG hA T s.val
    have hg : ∀ y' : T' ⟶ A, gs (lift σ y').left z ⊤ s.val = gs σ.left z ⊤ c0 := fun y' => by
      rw [← hc0]
      exact (gs_pull (lift σ y').left (fst T A).left z ⊤ trivial c0).trans (by rw [lift_fst_left])
    rw [hv, hv]
    apply Units.ext
    rw [← gs_unit _ z ⊤ trivial s, ← gs_unit _ z ⊤ trivial s, hg, hg]

theorem symLift_mul [IsCommMonObj A] (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {n : ℕ} (hn : Odd n)
    {a b : T ⟶ A} {Ua Ub Uab : ThetaGrp A L k T} {e : Γ(T.left, ⊤)ˣ} (ha : SymLift A L k n a Ua)
    (hb : SymLift A L k n b Ub) (hab : SymLift A L k n (a * b) Uab) (he : WeilIs A L k a b e) :
    ∃ r : Γ(T.left, ⊤)ˣ, r ^ 2 = e ∧ r ^ n = 1 ∧ ∀ s s₁ s₂ s₃ : LB.Sec (LPow A L k T), IsActOf A L k Ub s s₁ →
      IsActOf A L k Ua s₁ s₂ → IsActOf A L k Uab s s₃ → ∀ j, s₂.f j = liftFun A _ (r : Γ(T.left, ⊤)) * s₃.f j := by
  have t1 : ∀ (c : Γ(T.left, ⊤)) (s : (LPow A L k T).Sec) (j : (LPow A L k T).ι),
      (SecM.toSec A (c • SecM.ofSec A s)).f j = liftFun A _ c * s.f j := fun c s j => rfl
  obtain ⟨Θ, hΘpt, hΘ⟩ := GlobalTheory.ThetaAct.exists_mul hL Ua Ub
  have hpts : Uab.pt = Θ.pt := by rw [hΘpt, hab.pt_eq, ha.pt_eq, hb.pt_eq, mul_comm]
  obtain ⟨c, hc⟩ := GlobalTheory.ThetaAct.exists_ratio hG hA hL Uab Θ hpts
  have key : ∀ p : T.left, (gm (𝟙 T.left) p ⊤ c) ^ 2 = gm (𝟙 T.left) p ⊤ e ∧ (gm (𝟙 T.left) p ⊤ c) ^ n = 1 := by
    intro p
    obtain ⟨J, hJ, -⟩ := exists_good L hL p (K := Empty) Empty.elim Empty.elim (fun a => a.elim) (fun a => a.elim)
    have hfst : ∀ y : T ⟶ A, (lift (𝟙 T) y).left ≫ (fst T A).left = 𝟙 T.left := fun y => by
      rw [lift_fst_left, Over.id_left]
    have hm : ∀ y, tval Ua (lift (𝟙 T) y).left p J * tval Ub (lift (𝟙 T) (a * y)).left p J =
        gm (𝟙 T.left) p ⊤ c * tval Uab (lift (𝟙 T) y).left p J := fun y => by
      have h1 := hΘ _ (lift (𝟙 T) y).left p J hJ
      have h2 := hc _ (lift (𝟙 T) y).left p J hJ
      rw [lift_translT, Category.id_comp, ha.pt_eq] at h1
      rw [hfst, gs_unit _ p ⊤ trivial c] at h2
      rw [← h1]
      exact Units.ext (by rw [Units.val_mul]; exact h2)
    have hC : CommIsOf A L k Ua Ub e :=
      (GlobalTheory.GlobalLift.weilIs_iff_commIsOf hG hA hL Ua Ub e).mp (by rw [ha.pt_eq, hb.pt_eq]; exact he)
    have hcomm : ∀ y, tval Ua (lift (𝟙 T) y).left p J * tval Ub (lift (𝟙 T) (a * y)).left p J =
        tval Ub (lift (𝟙 T) y).left p J * tval Ua (lift (𝟙 T) (b * y)).left p J * gm (𝟙 T.left) p ⊤ e :=
      fun y => by
        have h1 := (GlobalTheory.CommPairing.commIsOf_iff hL Ua Ub e).mp hC _ (lift (𝟙 T) y).left p J hJ
        rw [lift_translT, lift_translT, Category.id_comp, Category.id_comp, ha.pt_eq, hb.pt_eq, hfst] at h1
        exact h1
    obtain ⟨nu, hnu, -⟩ := ha.sym
    have sa := fun y => sym_val' hG hA hL ha hnu (𝟙 T) hJ y
    have sb := fun y => sym_val' hG hA hL hb hnu (𝟙 T) hJ y
    have sc := fun y => sym_val' hG hA hL hab hnu (𝟙 T) hJ y
    simp only [Category.id_comp] at sa sb sc
    have hsq := sq_factor (fa := fun y => tval Ua (lift (𝟙 T) y).left p J)
      (fb := fun y => tval Ub (lift (𝟙 T) y).left p J) (fc := fun y => tval Uab (lift (𝟙 T) y).left p J)
      (ν := fun y => nval nu (lift (𝟙 T) y).left p J) (a := a) (b := b) hm hcomm sa sb sc
    refine ⟨hsq, ?_⟩
    have hcomm2 : ∀ y, tval Ua (lift (𝟙 T) y).left p J * tval Ub (lift (𝟙 T) (a * y)).left p J =
        tval Ub (lift (𝟙 T) y).left p J * tval Ua (lift (𝟙 T) (b * y)).left p J * gm (𝟙 T.left) p ⊤ c ^ 2 :=
      fun y => by rw [hsq]; exact hcomm y
    have pa := fun y => pow_val ha.pow_eq (𝟙 T) hJ y
    have pb := fun y => pow_val hb.pow_eq (𝟙 T) hJ y
    have pc := fun y => pow_val hab.pow_eq (𝟙 T) hJ y
    have hp := tval_periodic hG hA hL hb.pow_eq Ua (𝟙 T) hJ
    simp only [Category.id_comp, ha.pt_eq, hb.pt_eq, hab.pt_eq] at pa pb pc hp
    exact pow_factor (fa := fun y => tval Ua (lift (𝟙 T) y).left p J)
      (fb := fun y => tval Ub (lift (𝟙 T) y).left p J) (fc := fun y => tval Uab (lift (𝟙 T) y).left p J)
      (a := a) (b := b) hn hm hcomm2 pa pb pc hp
  refine ⟨c, unit_ext fun p _ => by rw [map_pow]; exact (key p).1,
    unit_ext fun p _ => by rw [map_pow, map_one]; exact (key p).2, ?_⟩
  intro s s₁ s₂ s₃ h1 h2 h3 j
  obtain ⟨w1, hw1⟩ := GlobalTheory.ThetaAct.exists_act hL Ub (SecM.ofSec A s)
  obtain ⟨w2, hw2⟩ := GlobalTheory.ThetaAct.exists_act hL Ua w1
  obtain ⟨w3, hw3⟩ := GlobalTheory.ThetaAct.exists_act hL Uab (SecM.ofSec A s)
  have e1 : SecM.ofSec A s₁ = w1 := GlobalTheory.ThetaAct.sv_ext hL fun y J hy => by
    rw [(GlobalTheory.ThetaAct.isActOf_iff hL Ub s s₁).mp h1 y J hy, hw1 _ (𝟙 _) y J hy]
  have e2 : SecM.ofSec A s₂ = w2 := GlobalTheory.ThetaAct.sv_ext hL fun y J hy => by
    rw [(GlobalTheory.ThetaAct.isActOf_iff hL Ua s₁ s₂).mp h2 y J hy, e1, hw2 _ (𝟙 _) y J hy]
  have e3 : SecM.ofSec A s₃ = w3 := GlobalTheory.ThetaAct.sv_ext hL fun y J hy => by
    rw [(GlobalTheory.ThetaAct.isActOf_iff hL Uab s s₃).mp h3 y J hy, hw3 _ (𝟙 _) y J hy]
  have hkey : w2 = (c : Γ(T.left, ⊤)) • w3 := GlobalTheory.ThetaAct.sv_ext hL fun y J hy => by
    rw [hw2 _ (𝟙 _) y J hy, hw1 _ _ y J hy, GlobalTheory.ThetaAct.sv_smul _ _ _ y hy, hw3 _ (𝟙 _) y J hy]
    have hθ := hΘ _ (𝟙 _) y J hy
    have hr := hc _ (𝟙 _) y J hy
    rw [hθ, Units.val_mul] at hr
    have htr : (𝟙 _ ≫ (translT A Ua.pt).left) ≫ (translT A Ub.pt).left = 𝟙 _ ≫ (translT A Uab.pt).left := by
      rw [Category.assoc, GlobalTheory.ThetaAct.translT_translT, ← hΘpt, ← hpts]
    rw [htr, ← _root_.mul_assoc, hr, _root_.mul_assoc]
  have fin : SecM.ofSec A s₂ = (c : Γ(T.left, ⊤)) • SecM.ofSec A s₃ := by rw [e2, hkey, e3]
  exact (congrArg (fun v => (SecM.toSec A v).f j) fin).trans (t1 _ _ _)

end GlobalTheory.SymLiftMul

namespace GlobalTheory

theorem moduli_univ_symLift_mul : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), Odd N → ∀ (T : Over Xo.X) (a b : T ⟶ Xo.univ.t.G) (Ua Ub Uab : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T) (e : Γ(T.left, ⊤)ˣ), SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) a Ua → SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) b Ub → SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) (a * b) Uab → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) a b e → ∃ r : Γ(T.left, ⊤)ˣ, r ^ 2 = e ∧ r ^ (N ^ 2) = 1 ∧ ∀ s s₁ s₂ s₃ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T), IsActOf Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) Ub s s₁ → IsActOf Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) Ua s₁ s₂ → IsActOf Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) Uab s s₃ → ∀ j, s₂.f j = liftFun Xo.univ.t.G _ (r : Γ(T.left, ⊤)) * s₃.f j := by
  intro hl E _ _ _ H Dw l Xo N hN T a b Ua Ub Uab e ha hb hab he
  have hP := GlobalTheory.moduli_univ_polAV E H Dw l Xo
  have hL : Xo.univ.t.PP.L.IsLB := by
    refine hP.2.2.2.2 (fun _ _ _ L _ => L.IsLB) fun P => ?_
    exact P.isLB
  exact GlobalTheory.SymLiftMul.symLift_mul hl.globalFns hP.2.2.2.1 hL hN.pow ha hb hab he

end GlobalTheory
