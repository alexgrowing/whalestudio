import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMetricOnLineGram
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.Mean4O

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.CombGen

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} {σ : F →+* ℂ}

def unitsAt (x : Y.X) : Subgroup Y.Fnˣ where
  carrier := {u | UnitAt x (u : Y.Fn)}
  mul_mem' {a b} ha hb := by
    show UnitAt x ((a * b : Y.Fnˣ) : Y.Fn)
    rw [Units.val_mul]
    exact UnitAt.mul ha hb
  one_mem' := by
    show UnitAt x ((1 : Y.Fnˣ) : Y.Fn)
    rw [Units.val_one]
    exact unitAt_one x
  inv_mem' {a} ha := by
    show UnitAt x ((a⁻¹ : Y.Fnˣ) : Y.Fn)
    rw [Units.val_inv_eq_inv_val]
    exact UnitAt.inv ha

def mkAt {x : Y.X} (a : Y.Fn) (ha : UnitAt x a) : unitsAt x := ⟨Units.mk0 a ha.ne_zero, ha⟩

theorem val_mkAt {x : Y.X} (a : Y.Fn) (ha : UnitAt x a) : (((mkAt a ha : unitsAt x) : Y.Fnˣ) : Y.Fn) = a := rfl

def logNormAt (z : Pts Y σ) : Additive (unitsAt (under z)) →+ ℝ where
  toFun u := Real.log ‖ratVal (((Additive.toMul u : unitsAt (under z)) : Y.Fnˣ) : Y.Fn) z‖
  map_zero' := by
    simp only [toMul_zero, OneMemClass.coe_one, Units.val_one, Base.ratVal_one, norm_one, Real.log_one]
  map_add' u v := by
    have hu : UnitAt (under z) (((Additive.toMul u : unitsAt (under z)) : Y.Fnˣ) : Y.Fn) := (Additive.toMul u).2
    have hv : UnitAt (under z) (((Additive.toMul v : unitsAt (under z)) : Y.Fnˣ) : Y.Fn) := (Additive.toMul v).2
    simp only [toMul_add, Subgroup.coe_mul, Units.val_mul]
    rw [ratVal_mul hu.regAt hv.regAt, norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 (ratVal_ne_zero hu)) (norm_ne_zero_iff.2 (ratVal_ne_zero hv))]

theorem logNormAt_mkAt (z : Pts Y σ) (a : Y.Fn) (ha : UnitAt (under z) a) :
    logNormAt z (Additive.ofMul (mkAt a ha)) = Real.log ‖ratVal a z‖ := rfl

theorem lnN_eq_add {Δ : Y.Dv} {m : C.Met Y σ Δ} {f : Y.Fn} {z : Pts Y σ} (hp : PosAt m z)
    (hf : Δ.GeneratesAt (under z) f) :
    lnN m f z = lnN m (genAt Δ (under z)) z + Real.log ‖ratVal (f * (genAt Δ (under z))⁻¹) z‖ := by
  have hu : UnitAt (under z) (f * (genAt Δ (under z))⁻¹) :=
    GlobalTheory.ChernWeilLine.unitAt_mul_inv_of_generatesAt hf (generatesAt_genAt Δ _)
  have hg0 : genAt Δ (under z) ≠ 0 := Units.ne_zero _
  have e : C.pn Y σ Δ m (C.cx Y σ f) z =
      ‖ratVal (f * (genAt Δ (under z))⁻¹) z‖ ^ 2 * C.pn Y σ Δ m (C.cx Y σ (genAt Δ (under z))) z := by
    conv_lhs => rw [← inv_mul_cancel_right₀ hg0 f]
    exact C.pn_mul Y σ Δ m _ _ z hu.regAt (generatesAt_genAt Δ _).regularAt
  have hr : ‖ratVal (f * (genAt Δ (under z))⁻¹) z‖ ≠ 0 := norm_ne_zero_iff.2 (ratVal_ne_zero hu)
  simp only [lnN]
  rw [e, Real.log_mul (pow_ne_zero 2 hr) (ne_of_gt hp), Real.log_pow]
  push_cast
  ring

end GlobalTheory.Mean4O.CombGen

namespace GlobalTheory.Mean4O.CombGen

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem div_prod_eq {ι : Type} [Fintype ι] (q : ℕ) (b : ι → ℤ) (fM gM : Y.Fn) (f g : ι → Y.Fn) (hgM : gM ≠ 0)
    (hg : ∀ i, g i ≠ 0) :
    fM ^ q / ∏ i, f i ^ b i = (gM ^ q / ∏ i, g i ^ b i) * (fM * gM⁻¹) ^ q / ∏ i, (f i * (g i)⁻¹) ^ b i := by
  have hG : ∏ i, g i ^ b i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hg i)
  have e : ∏ i, (f i * (g i)⁻¹) ^ b i = (∏ i, f i ^ b i) * (∏ i, g i ^ b i)⁻¹ := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [mul_zpow, inv_zpow]
  rw [e, mul_pow, inv_pow]
  have hq : gM ^ q ≠ 0 := pow_ne_zero _ hgM
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv, inv_inv]
  calc fM ^ q * (∏ i, f i ^ b i)⁻¹
      = fM ^ q * (∏ i, f i ^ b i)⁻¹ * (gM ^ q * (gM ^ q)⁻¹) * ((∏ i, g i ^ b i)⁻¹ * ∏ i, g i ^ b i) := by
        rw [mul_inv_cancel₀ hq, inv_mul_cancel₀ hG, mul_one, mul_one]
    _ = _ := by ring

end GlobalTheory.Mean4O.CombGen

open GlobalTheory.Mean4O.CombGen in
theorem GlobalTheory.Mean4O.CombGen.lnAdl_comb_change : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (ι : Type) [Fintype ι] (Mb : Adl (cxSt F) Y) (ρ : ι → Adl (cxSt F) Y) (q : ℕ) (b : ι → ℤ) (σ : F →+* ℂ) (z : Pts Y σ) (gz : ℝ) (fM : Y.Fn) (f : ι → Y.Fn), PosAt (Mb.m σ) z → (∀ i, PosAt ((ρ i).m σ) z) → (q : ℝ) * lnAdl Mb σ z = Real.log ‖ratVal (genAt Mb.D (under z) ^ q / ∏ i, genAt (ρ i).D (under z) ^ b i) z‖ + ∑ i, (b i : ℝ) * lnAdl (ρ i) σ z - q * ((Mb.n : ℕ) : ℝ) * gz → Mb.D.GeneratesAt (under z) fM → (∀ i, (ρ i).D.GeneratesAt (under z) (f i)) → UnitAt (under z) (genAt Mb.D (under z) ^ q / ∏ i, genAt (ρ i).D (under z) ^ b i) → UnitAt (under z) (fM ^ q / ∏ i, f i ^ b i) → (q : ℝ) * lnN (Mb.m σ) fM z = Real.log ‖ratVal (fM ^ q / ∏ i, f i ^ b i) z‖ + ∑ i, (b i : ℝ) * lnN ((ρ i).m σ) (f i) z - q * ((Mb.n : ℕ) : ℝ) * gz + ((q : ℝ) * ((Mb.n : ℕ) : ℝ) * Mb.ci (InfinitePlace.mk σ) - ∑ i, (b i : ℝ) * (((ρ i).n : ℕ) : ℝ) * (ρ i).ci (InfinitePlace.mk σ)) := by
  intro F _ _ Y ι _ Mb ρ q b σ z gz fM f hpM hp hyp hfM hf hk hh
  set x := under z with hx
  set gM := genAt Mb.D x with hgM
  set g : ι → Y.Fn := fun i => genAt (ρ i).D x with hg
  have huM : UnitAt x (fM * gM⁻¹) := GlobalTheory.ChernWeilLine.unitAt_mul_inv_of_generatesAt hfM (generatesAt_genAt _ _)
  have hu : ∀ i, UnitAt x (f i * (g i)⁻¹) := fun i =>
    GlobalTheory.ChernWeilLine.unitAt_mul_inv_of_generatesAt (hf i) (generatesAt_genAt _ _)
  have hgM0 : gM ≠ 0 := Units.ne_zero _
  have hg0 : ∀ i, g i ≠ 0 := fun i => Units.ne_zero _

  have eS : mkAt (fM ^ q / ∏ i, f i ^ b i) hh =
      mkAt (gM ^ q / ∏ i, g i ^ b i) hk * mkAt (fM * gM⁻¹) huM ^ q / ∏ i, mkAt (f i * (g i)⁻¹) (hu i) ^ b i := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_zpow, Subgroup.val_finset_prod,
      Units.val_div_eq_div_val, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, Units.coe_prod,
      val_mkAt]
    exact div_prod_eq q b fM gM f g hgM0 hg0
  have eL : Real.log ‖ratVal (fM ^ q / ∏ i, f i ^ b i) z‖ = Real.log ‖ratVal (gM ^ q / ∏ i, g i ^ b i) z‖ +
      (q : ℝ) * Real.log ‖ratVal (fM * gM⁻¹) z‖ - ∑ i, (b i : ℝ) * Real.log ‖ratVal (f i * (g i)⁻¹) z‖ := by
    rw [← logNormAt_mkAt z _ hh, eS, ← logNormAt_mkAt z _ hk, ← logNormAt_mkAt z _ huM]
    simp only [ofMul_div, ofMul_mul, ofMul_pow, ofMul_prod, ofMul_zpow, map_sub, map_add, map_nsmul, map_sum, map_zsmul,
      nsmul_eq_mul, zsmul_eq_mul, logNormAt_mkAt]
    rfl
  have e1 := lnN_eq_add hpM hfM
  have e2 : ∀ i, lnN ((ρ i).m σ) (f i) z = lnN ((ρ i).m σ) (g i) z + Real.log ‖ratVal (f i * (g i)⁻¹) z‖ :=
    fun i => lnN_eq_add (hp i) (hf i)
  have s1 : ∑ i, (b i : ℝ) * lnN ((ρ i).m σ) (f i) z =
      ∑ i, (b i : ℝ) * lnN ((ρ i).m σ) (g i) z + ∑ i, (b i : ℝ) * Real.log ‖ratVal (f i * (g i)⁻¹) z‖ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [e2 i]; ring
  have s2 : ∑ i, (b i : ℝ) * lnAdl (ρ i) σ z =
      ∑ i, (b i : ℝ) * lnN ((ρ i).m σ) (g i) z - ∑ i, (b i : ℝ) * (((ρ i).n : ℕ) : ℝ) * (ρ i).ci (InfinitePlace.mk σ) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [lnAdl, g]; ring
  have hM : lnAdl Mb σ z = lnN (Mb.m σ) gM z - ((Mb.n : ℕ) : ℝ) * Mb.ci (InfinitePlace.mk σ) := rfl
  rw [hM, s2] at hyp
  rw [eL, s1, e1]
  linear_combination hyp
