import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PsiWeightZeroLinearCombination

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out.InhTate
open GlobalTheory.Toroidal GlobalTheory.ToricData

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigChart.Model

theorem gm_gv {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (V : Y.Opens) (h : r z ∈ V) (a : Γ(Y, ⊤)ˣ) :
    gm r z V (InhTate.gv a V) = gm (𝟙 Z) z ⊤ (pullTop r a) := by
  rw [InhTate.gv, gm_res r z _ h]
  have := gm_pull (𝟙 Z) r z ⊤ trivial a
  rw [Category.id_comp] at this
  exact this.symm

theorem val_const {W Y Z : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ W)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb (Inh.trivLB W) φ ε)} {a : Γ(Y, ⊤)ˣ} (h : IsConst t a) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ W) → (Inh.trivLB W).ι) : Geo.Tor.val t r z J = gm (𝟙 Z) z ⊤ (pullTop r a) := by
  have hm : r z ∈ LB.wchart (Inh.trivLB W) φ (fun k => J (r ≫ φ k)) := by rw [wchart_triv]; trivial
  exact (congrArg (gm r z _) (h _)).trans (gm_gv r z _ hm a)

theorem pullTop_id {Z : Scheme.{0}} (a : Γ(Z, ⊤)ˣ) : pullTop (𝟙 Z) a = a := by
  ext; simp [pullTop]

theorem good_triv {W Z : Scheme.{0}} (z : Z) : Good (Inh.trivLB W) z (fun _ => PUnit.unit) := fun _ => trivial

theorem gm_eq_of_top {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {V : Y.Opens} (hV : V = ⊤) (a : Γ(Y, V)ˣ) :
    gm r z V a = gm (𝟙 Z) z ⊤ (pullTop r (res hV.ge a)) := by
  subst hV
  rw [← gm_gv r z (⊤ : Y.Opens) (show r z ∈ (⊤ : Y.Opens) from trivial), InhTate.gv, res_self, res_self]

theorem one_isGen {W Y : Scheme.{0}} (f g : Y ⟶ W) :
    LB.Gen.IsGen (⟨fun _ => 1⟩ : LB.Iso ((Inh.trivLB W).pull f) ((Inh.trivLB W).pull g)) := by
  intro i j
  have hg : (LB.div ((Inh.trivLB W).pull g) ((Inh.trivLB W).pull f)).g i j = 1 := by
    have h₁ := Inh.linComb_triv_g (fun _ : PUnit => f) (fun _ => 1) i.2 j.2
    have h₂ := Inh.linComb_triv_g (fun _ : PUnit => g) (fun _ => 1) i.1 j.1
    unfold LB.div
    dsimp only
    rw [h₁, h₂, map_one, map_one, inv_one, _root_.mul_one]
  rw [hg, _root_.one_mul]
  rfl

theorem constHom_apply {R k : Type} [CommRing R] [Field k] (ρ : R →+* DualNumber k) (r : R) :
    constHom ρ r = TrivSqZeroExt.inl (ρ r).fst := rfl

theorem fst_constHom {R k : Type} [CommRing R] [Field k] (ρ : R →+* DualNumber k) :
    spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap ρ =
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (constHom ρ) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

variable {R : Type} [CommRing R] [IsDomain R] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  (q : X → (FractionRing R)ˣ) {m : ℕ} (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ X)

theorem isUnitTau_iff (y z : X) (τ₀) :
    IsUnitTau (toricPre R X q) t gam y z τ₀ ↔ ∃ u : Rˣ, IsConst τ₀ (unitOn u) ∧
      (polar q y z : FractionRing R) = (∏ i, algebraMap R (FractionRing R) (t i) ^ gam i y z) * algebraMap R _ u := by
  have key : ∀ (u : Rˣ) (e : (FractionRing R)ˣ), IsConst τ₀ (unitOn u) → ∀ z J,
      gm (𝟙 (TK R).left) z ⊤ (unitOn e) * val τ₀ (toUnit (TK R)).left z J =
      gm (𝟙 (TK R).left) z ⊤ (unitOn (e * Units.map (algebraMap R (FractionRing R)).toMonoidHom u)) := by
    intro u e hu z J
    rw [unitOn_mul, map_mul, ← pullTop_unitOn]
    exact congrArg _ (val_const hu _ z J)
  have key2 : ∀ x J, val ((toricPre R X q).tau y z) (𝟙 _) x J = gm (𝟙 (TK R).left) x ⊤ (unitOn (polar q y z)) := by
    intro x J
    exact (val_const (tau_isConst q y z) _ x J).trans (congrArg _ (pullTop_id _))
  constructor
  · rintro ⟨-, e, he, h⟩
    obtain ⟨a, ha⟩ := exists_isConst τ₀
    obtain ⟨u, rfl⟩ := unitOn_bijective.2 a
    refine ⟨u, ha, ?_⟩
    have : unitOn (polar q y z) = unitOn (e * Units.map (algebraMap R (FractionRing R)).toMonoidHom u) :=
      unit_ext fun x _ => (key2 x _).symm.trans ((h x _ (good_triv x)).trans (key u e ha x _))
    rw [unitOn_inj.1 this, Units.val_mul, he]
    rfl
  · rintro ⟨u, hu, hq⟩
    refine ⟨?_, polar q y z * (Units.map (algebraMap R (FractionRing R)).toMonoidHom u)⁻¹, ?_, fun x J _ => ?_⟩
    · rw [gen_eq_of_isConst hu (cg_isConst _ _ _)]; exact cg_isGen _ _ _
    · rw [Units.val_mul, hq, _root_.mul_assoc]
      have : algebraMap R (FractionRing R) u * ((Units.map (algebraMap R (FractionRing R)).toMonoidHom u)⁻¹ : (FractionRing R)ˣ) = 1 :=
        (Units.map (algebraMap R (FractionRing R)).toMonoidHom u).mul_inv
      rw [this, _root_.mul_one]
      rfl
    · rw [key u _ hu, key2, inv_mul_cancel_right]

theorem isConstAlong_iff {k : Type} [Field k] (ρ : R →+* DualNumber k) (a : Fin m → k) :
    IsConstAlong (toricPre R X q) t gam ρ a ↔ ∀ (y z : X) (u : Rˣ),
      (polar q y z : FractionRing R) = (∏ i, algebraMap R (FractionRing R) (t i) ^ gam i y z) * algebraMap R _ u →
      ρ u = ((1 : DualNumber k) + (TrivSqZeroExt.inr (∑ i, a i * gam i y z) : DualNumber k)) * constHom ρ u := by
  have unit : ∀ x : k, ∃ e : (DualNumber k)ˣ, (e : DualNumber k) = 1 + TrivSqZeroExt.inr x := fun x =>
    ⟨⟨1 + TrivSqZeroExt.inr x, 1 - TrivSqZeroExt.inr x, by ext <;> simp, by ext <;> simp⟩, rfl⟩
  constructor
  · rintro ⟨B', _, π₁, π₂, w, c', h₁, -, -, -, hc, h⟩
    have : IsIso B'.hom := by
      have : IsIso (toricPre R X q).P.A.hom := by show IsIso (𝟙 _); infer_instance
      exact h₁.1.isIso_snd_of_isIso
    have hc' : ∀ y, c' y = inv B'.hom := fun y => by
      rw [← cancel_mono B'.hom, (hc y).1, IsIso.inv_hom_id]
    obtain rfl : c' = fun _ => inv B'.hom := funext hc'
    intro y z u hq
    obtain ⟨e, he⟩ := unit (∑ i, a i * gam i y z)
    have hu := cg_isConst (K := Fin 4) ![((toricPre R X q).c (y + z)).left, ((toricPre R X q).c y).left,
      ((toricPre R X q).c z).left, ((toricPre R X q).c 0).left] ![-1, 1, 1, -1] (unitOn u)
    have H := h y z _ ((isUnitTau_iff q t gam y z _).2 ⟨u, hu, hq⟩) e he
    have : unitOn (Units.map ρ.toMonoidHom u) = unitOn (e * Units.map (constHom ρ).toMonoidHom u) := by
      refine unit_ext fun x _ => ?_
      have H' := H x _ (good_triv x)
      rw [unitOn_mul, map_mul, ← pullTop_unitOn, ← pullTop_unitOn]
      refine (val_const hu _ x _).symm.trans (H'.trans (congrArg₂ (· * ·) ?_ (val_const hu _ x _)))
      rw [mul_inv_cancel, _root_.one_mul, inv_mul_cancel, _root_.one_mul]
    have := congrArg Units.val (unitOn_inj.1 this)
    erw [← he]
    simpa using this
  · intro h
    have pb : ∀ f : Sp (DualNumber k) ⟶ Sp R, IsGrpPullback (𝟙_ (Over (Sp (DualNumber k)))) (𝟙_ (Over (Sp R))) f f := fun f =>
      ⟨IsPullback.of_vert_isIso (fst := f) (snd := 𝟙 _) (f := 𝟙 _) (g := f) ⟨by simp⟩, fun T x y x₀ y₀ hx _ => by
        rw [toUnit_unique (x₀ * y₀) x₀, toUnit_unique (x * y) x, hx]⟩
    have hc : ∀ y, ((toricPre R X q).c y).left = 𝟙 (Sp R) := fun y =>
      congrArg (·.left) (toUnit_unique ((toricPre R X q).c y) (𝟙 (𝟙_ (Over (Sp R)))))
    refine ⟨𝟙_ _, inferInstance, spMap ρ, spMap (constHom ρ), ⟨fun _ => 1⟩, fun _ => 𝟙 _, pb _, pb _, ?_, ?_,
      fun y => ⟨Category.id_comp _, ?_, ?_⟩, ?_⟩
    · intro Z x y hx
      have hx' : x = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom := (Category.comp_id x).symm.trans hx
      subst hx'
      exact (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) (fst_constHom ρ)).trans (Category.assoc _ _ _).symm)
    · intro i j
      exact one_isGen _ _ i j
    · exact (Category.id_comp _).trans ((Category.comp_id _).symm.trans (congrArg _ (hc y).symm))
    · exact (Category.id_comp _).trans ((Category.comp_id _).symm.trans (congrArg _ (hc y).symm))
    · intro y z τ₀ hτ e he x J _
      obtain ⟨u, hu, hq⟩ := (isUnitTau_iff q t gam y z _).1 hτ
      have : Units.map ρ.toMonoidHom u = e * Units.map (constHom ρ).toMonoidHom u := by
        ext1
        have := h y z u hq
        erw [← he] at this
        simpa using this
      refine (val_const hu _ x J).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_const hu _ x J).symm))
      simp only [map_one, inv_one, _root_.one_mul]
      erw [pullTop_unitOn, pullTop_unitOn]
      rw [this, unitOn_mul _ (Units.map _ _), map_mul]

abbrev A : Type := PowerSeries (PowerSeries ℚ)

abbrev tt : A := PowerSeries.X

abbrev ss : A := PowerSeries.C PowerSeries.X

theorem ss_mem : ss ∈ maximalIdeal A := by
  rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_C,
    PowerSeries.isUnit_iff_constantCoeff]
  simp

theorem isUnit_one_add {x : A} (h : x ∈ maximalIdeal A) : IsUnit (1 + x) := by
  have := isUnit_one_sub_self_of_mem_nonunits (-x) ((mem_maximalIdeal _).1 (neg_mem h))
  simpa using this

def frm : LinearMap.BilinForm ℤ (ℤ × ℤ) := LinearMap.mk₂ ℤ (fun y z => 2 * (y.1 * z.1 + y.2 * z.2))
  (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)

def nrm (y : ℤ × ℤ) : ℕ := (y.1 * y.1 + y.2 * y.2).toNat

theorem frm_self (y : ℤ × ℤ) : frm y y = 2 * nrm y := by
  have : 0 ≤ y.1 * y.1 + y.2 * y.2 := add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  simp only [frm, nrm, LinearMap.mk₂_apply, Int.toNat_of_nonneg this]

def per (v : Aˣ) (b : ℤ × ℤ → ℤ) (y : ℤ × ℤ) : (FractionRing A)ˣ :=
  Units.mk0 (algebraMap A _ (tt ^ nrm y * (v ^ b y : Aˣ)))
    ((map_ne_zero_iff _ (IsFractionRing.injective A _)).2
      (mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (Units.ne_zero _)))

theorem nrm_cast (y : ℤ × ℤ) : (nrm y : ℤ) = y.1 * y.1 + y.2 * y.2 :=
  Int.toNat_of_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))

theorem polar_per (v : Aˣ) (b : ℤ × ℤ → ℤ) (y z : ℤ × ℤ) :
    (polar (per v b) y z : FractionRing A) =
      algebraMap A (FractionRing A) tt ^ frm y z * algebraMap A _ (v ^ (b (y + z) - b y - b z) : Aˣ) := by
  have ht : algebraMap A (FractionRing A) tt ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A _)).2 PowerSeries.X_ne_zero
  have hv : ∀ n : ℤ, algebraMap A (FractionRing A) (v ^ n : Aˣ) = algebraMap A (FractionRing A) v ^ n := fun n =>
    (congrArg Units.val (map_zpow (Units.map (algebraMap A (FractionRing A)).toMonoidHom) v n)).trans
      (Units.val_zpow_eq_zpow_val _ _)
  have hv0 : algebraMap A (FractionRing A) v ≠ 0 := (v.isUnit.map _).ne_zero
  have e : frm y z = nrm (y + z) - nrm y - nrm z := by
    simp only [nrm_cast, frm, LinearMap.mk₂_apply, Prod.fst_add, Prod.snd_add]; ring
  simp only [polar, per, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, map_mul, map_pow, hv, e, zpow_sub₀ ht,
    zpow_sub₀ hv0, zpow_natCast]
  field_simp

theorem isConstAlong_per_iff (v : Aˣ) (b : ℤ × ℤ → ℤ) {k : Type} [Field k] (ρ : A →+* DualNumber k) (a : Fin 1 → k) :
    IsConstAlong (toricPre A (ℤ × ℤ) (per v b)) ![tt] ![frm] ρ a ↔ ∀ y z : ℤ × ℤ,
      ρ (v ^ (b (y + z) - b y - b z) : Aˣ) = ((1 : DualNumber k) + (TrivSqZeroExt.inr (a 0 * frm y z) : DualNumber k)) *
        constHom ρ (v ^ (b (y + z) - b y - b z) : Aˣ) := by
  refine (isConstAlong_iff (per v b) ![tt] ![frm] ρ a).trans (forall₂_congr fun y z => ⟨fun h => ?_, ?_⟩)
  · simpa using h (v ^ (b (y + z) - b y - b z)) (by simpa using polar_per v b y z)
  · intro h u hq
    have ht : algebraMap A (FractionRing A) tt ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A _)).2 PowerSeries.X_ne_zero
    rw [polar_per, Fin.prod_univ_one] at hq
    have hu := IsFractionRing.injective A (FractionRing A) (mul_left_cancel₀ (zpow_ne_zero _ ht) hq)
    rw [← hu]
    simpa using h

def tang : A →+* DualNumber ℚ := RingHom.comp
  { toFun := fun f : PowerSeries ℚ => TrivSqZeroExt.inl (PowerSeries.constantCoeff f) + TrivSqZeroExt.inr (PowerSeries.coeff 1 f)
    map_one' := by ext <;> simp [PowerSeries.coeff_one]
    map_mul' := fun f g => by
      ext
      · simp
      · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_inl,
          TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, PowerSeries.coeff_mul]
        rw [Finset.Nat.antidiagonal_succ]
        first
          | (simp [PowerSeries.coeff_zero_eq_constantCoeff]; done)
          | (simp [PowerSeries.coeff_zero_eq_constantCoeff]; ring)
    map_zero' := by ext <;> simp
    map_add' := fun f g => by ext <;> simp [add_add_add_comm] } PowerSeries.constantCoeff

theorem tang_tt : tang tt = 0 := by ext <;> simp [tang]

theorem tang_ss : tang ss = TrivSqZeroExt.inr 1 := by ext <;> simp [tang]

theorem tang_max (r : A) (hr : r ∈ maximalIdeal A) : (tang r).fst = 0 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff,
    PowerSeries.isUnit_iff_constantCoeff] at hr
  simpa [tang] using hr

theorem not_isRigid_of {Q : DegPre A} {gam : Fin 1 → LinearMap.BilinForm ℤ Q.X} {a : Fin 1 → ℚ}
    (h : IsConstAlong Q ![tt] gam tang a) : ¬ IsRigid Q ![tt] gam := fun H => by
  have := H ℚ tang a tang_max (fun i => by fin_cases i; exact tang_tt) h ss
  simp [tang_ss] at this

def vs : Aˣ := (isUnit_one_add ss_mem).unit

def vts : Aˣ := (isUnit_one_add (Ideal.mul_mem_left _ tt ss_mem)).unit

theorem isRigid_mixed : IsRigid (toricPre A (ℤ × ℤ) (per vs fun y => y.1 * y.2)) ![tt] ![frm] := by
  intro k _ ρ a hm ht hc r
  have h := (isConstAlong_per_iff _ _ ρ a).1 hc (1, 0) (0, 1)
  have hs : ρ ss = 0 := by
    have := congrArg TrivSqZeroExt.snd h
    ext
    · exact hm _ ss_mem
    · simpa [vs, frm, constHom_apply] using this
  have ht' : ρ tt = 0 := ht 0
  have hq : ∀ c : ℚ, (ρ (PowerSeries.C (PowerSeries.C c))).snd = 0 := fun c => by
    have := congrArg (fun f : ℚ →+* DualNumber k => (f c).snd)
      (RingHom.ext_rat (ρ.comp (PowerSeries.C.comp PowerSeries.C)) ((constHom ρ).comp (PowerSeries.C.comp PowerSeries.C)))
    simpa [constHom_apply] using this
  rw [PowerSeries.eq_X_mul_shift_add_const r, PowerSeries.eq_X_mul_shift_add_const (PowerSeries.constantCoeff r),
    map_add, map_mul, ht', map_add, map_mul, map_add, map_mul, hs]
  simpa using hq _

theorem not_isRigid_blowup : ¬ IsRigid (toricPre A (ℤ × ℤ) (per vts fun y => y.1 * y.2)) ![tt] ![frm] := by
  refine not_isRigid_of (a := 0) ((isConstAlong_per_iff _ _ _ _).2 fun y z => ?_)
  have : Units.map tang.toMonoidHom vts = 1 := by ext1; simp [vts, tang_tt]
  have h : ∀ n : ℤ, tang (vts ^ n : Aˣ) = 1 := fun n =>
    calc tang (vts ^ n : Aˣ) = ((Units.map tang.toMonoidHom (vts ^ n) : (DualNumber ℚ)ˣ) : DualNumber ℚ) := rfl
      _ = 1 := by rw [map_zpow, this, one_zpow, Units.val_one]
  rw [constHom_apply, h]
  simp

theorem tang_vs_zpow (n : ℤ) : tang (vs ^ n : Aˣ) = 1 + TrivSqZeroExt.inr (n : ℚ) := by
  have h : ∀ n : ℕ, tang (vs ^ (n : ℤ) : Aˣ) = 1 + TrivSqZeroExt.inr (n : ℚ) := fun n => by
    rw [zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
    have : tang vs = 1 + TrivSqZeroExt.inr 1 := by simp [vs, tang_ss]
    rw [this]
    ext <;> simp [TrivSqZeroExt.snd_pow]
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using h n
  · have e : tang (vs ^ (-(n : ℤ)) : Aˣ) * tang (vs ^ (n : ℤ) : Aˣ) = 1 := by
      rw [← map_mul, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, map_one]
    rw [h] at e
    have e' : ((1 : DualNumber ℚ) + TrivSqZeroExt.inr (n : ℚ)) * (1 + TrivSqZeroExt.inr (-(n : ℚ))) = 1 := by
      ext <;> simp
    rw [← _root_.mul_one (tang _), ← e', ← _root_.mul_assoc, e, _root_.one_mul]
    ext <;> simp

theorem not_isRigid_cone : ¬ IsRigid (toricPre A (ℤ × ℤ) (per vs fun y => nrm y)) ![tt] ![frm] := by
  refine not_isRigid_of (a := 1) ((isConstAlong_per_iff _ _ _ _).2 fun y z => ?_)
  have e : frm y z = nrm (y + z) - nrm y - nrm z := by
    simp only [nrm_cast, frm, LinearMap.mk₂_apply, Prod.fst_add, Prod.snd_add]; ring
  rw [constHom_apply, tang_vs_zpow, ← e]
  ext <;> simp

theorem not_isConstAlong_cone_zero :
    ¬ IsConstAlong (toricPre A (ℤ × ℤ) (per vs fun y => nrm y)) ![tt] ![frm] tang 0 := by
  intro hc
  have h := (isConstAlong_per_iff _ _ _ _).1 hc (1, 0) (1, 0)
  rw [constHom_apply, tang_vs_zpow] at h
  have := congrArg TrivSqZeroExt.snd h
  simp [nrm] at this

theorem isConstAlong_const (Q : DegPre R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X) {k : Type} [Field k]
    (ρ : R →+* DualNumber k) (hρ : constHom ρ = ρ) : IsConstAlong Q t gam ρ 0 := by
  unfold IsConstAlong
  rw [hρ]
  have hL : (Q.P.L.pull (pullback.fst Q.P.A.hom (spMap ρ))).IsLB := LB.isLB_linComb Q.P.isLB _ _
  have hw : ∀ y, (spMap ρ ≫ (Q.c y).left) ≫ Q.P.A.hom = 𝟙 _ ≫ spMap ρ := fun y => by
    rw [Category.assoc, Over.w (Q.c y)]; exact (Category.comp_id _).trans (Category.id_comp _).symm
  refine ⟨(Over.pullback (spMap ρ)).obj Q.P.A, inferInstance, pullback.fst _ _, pullback.fst _ _, idIso _,
    fun y => pullback.lift _ _ (hw y), isGrpPullback_pullback _ _, isGrpPullback_pullback _ _, fun _ _ _ _ => rfl,
    idIso_isGen hL, fun y => ⟨pullback.lift_snd _ _ _, pullback.lift_fst _ _ _, pullback.lift_fst _ _ _⟩,
    fun y z τ₀ _ e he x J hJ => ?_⟩
  obtain rfl : e = 1 := Units.ext (by simpa using he)
  have k : ∀ f : Sp (DualNumber k) ⟶ pullback Q.P.A.hom (spMap ρ),
      gm f x _ ((idIso (Q.P.L.pull (pullback.fst Q.P.A.hom (spMap ρ)))).s
        (fun _ => J (f ≫ pullback.fst Q.P.A.hom (spMap ρ)), fun _ => J (f ≫ pullback.fst Q.P.A.hom (spMap ρ)))) = 1 :=
    fun f => gm_self hL f x (mem_pull.2 (hJ (f ≫ _)))
  erw [k, k, k, k, unitOn_one, map_one]
  simp

theorem toroidalChartsForFan (h : RigidForFan) : GlobalTheory.Published.ToroidalChartsForFan := by
  intro E _ _ _ H Dw hr φ h₁ h₂ l Xo c
  obtain ⟨Y, BD, d, k, a₁, a₂, a₃, a₄, a₅, a₆, a₇, -⟩ := h E H Dw hr φ h₁ h₂ l Xo c
  exact ⟨Y, BD, d, k, a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩

theorem isMonomial_per (v : Aˣ) (b : ℤ × ℤ → ℤ) :
    IsMonomial (toricPre A (ℤ × ℤ) (per v b)) ![tt] (![frm] : Fin 1 → LinearMap.BilinForm ℤ (ℤ × ℤ)) := by
  intro (y : ℤ × ℤ)
  refine ⟨v ^ b y, ![nrm y], fun i => by fin_cases i; exact frm_self y, fun _ => PUnit.unit, le_rfl,
    PsiCoordLocal.generic_le _ _ _ le_rfl, ToricData.psi_eq_toOpen _ y _ ?_ _ _ _⟩
  simp only [per, Units.val_mk0, Fin.prod_univ_one, Matrix.cons_val_zero, mul_comm]

end GlobalTheory.RigChart.Model
