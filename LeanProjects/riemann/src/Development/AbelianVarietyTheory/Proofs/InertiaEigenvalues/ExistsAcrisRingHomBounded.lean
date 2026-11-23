import Mathlib
import Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSeedDiscNormBoundsStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.AcrisDisc

section General

variable {l : ℕ} {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0}

theorem norm_add_le_max_disc (x y : Disc l u ρ) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  refine (denseRange_ofPre l u ρ).induction_on₂ (p := fun x y : Disc l u ρ => ‖x + y‖ ≤ max ‖x‖ ‖y‖) ?_ ?_ x y
  · exact isClosed_le (continuous_norm.comp (continuous_fst.add continuous_snd))
      ((continuous_norm.comp continuous_fst).max (continuous_norm.comp continuous_snd))
  · intro a b
    rw [← map_add, norm_ofPre, norm_ofPre, norm_ofPre]
    exact gauge_add_le_max l u ρ a b

def unitBall (l : ℕ) (u : A) (ρ : ℝ≥0) : Subring (Disc l u ρ) where
  carrier := {x | ‖x‖ ≤ 1}
  zero_mem' := by simp
  one_mem' := by
    show ‖(1 : Disc l u ρ)‖ ≤ 1
    simpa using norm_toDisc_le (l := l) (u := u) (ρ := ρ) (1 : A)
  add_mem' {x y} hx hy := (norm_add_le_max_disc x y).trans (max_le hx hy)
  mul_mem' {x y} hx hy := (norm_mul_le x y).trans (mul_le_one₀ hx (norm_nonneg _) hy)
  neg_mem' {x} hx := by simpa using hx

end General

section Complete

variable {l : ℕ} [hl : Fact l.Prime] {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0}

theorem norm_lpow_mul (hL : ∀ y : Disc l u ρ, ‖(l : Disc l u ρ) * y‖ = (l : ℝ)⁻¹ * ‖y‖) (n : ℕ)
    (y : Disc l u ρ) : ‖(l : Disc l u ρ) ^ n * y‖ = (l : ℝ)⁻¹ ^ n * ‖y‖ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_assoc, hL, ih, pow_succ']; ring

theorem inv_l_lt_one : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.out.one_lt)

namespace UnitBall
open Filter Topology

theorem norm_le_one_of_mem (x : unitBall l u ρ) : ‖(x : Disc l u ρ)‖ ≤ 1 := x.2

theorem norm_pow_mul (hmul : ∀ y : Disc l u ρ, ‖(l : Disc l u ρ) * y‖ = (l : ℝ)⁻¹ * ‖y‖) (n : ℕ)
    (y : Disc l u ρ) : ‖(l : Disc l u ρ) ^ n * y‖ = ((l : ℝ)⁻¹) ^ n * ‖y‖ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_assoc, hmul, ih, pow_succ']; ring

theorem mem_smul_top_iff (n : ℕ) (x : unitBall l u ρ) :
    x ∈ (Ideal.span {((l : ℕ) : unitBall l u ρ)}) ^ n • (⊤ : Submodule (unitBall l u ρ) (unitBall l u ρ)) ↔
      ∃ a : unitBall l u ρ, a * ((l : ℕ) : unitBall l u ρ) ^ n = x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']

theorem inv_pow_pos (n : ℕ) : (0 : ℝ) < ((l : ℝ)⁻¹) ^ n := by
  have : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  positivity

theorem norm_le_of_mem (hmul : ∀ y : Disc l u ρ, ‖(l : Disc l u ρ) * y‖ = (l : ℝ)⁻¹ * ‖y‖) (n : ℕ)
    (x : unitBall l u ρ)
    (hx : x ∈ (Ideal.span {((l : ℕ) : unitBall l u ρ)}) ^ n • (⊤ : Submodule (unitBall l u ρ) (unitBall l u ρ))) :
    ‖(x : Disc l u ρ)‖ ≤ ((l : ℝ)⁻¹) ^ n := by
  obtain ⟨a, rfl⟩ := (mem_smul_top_iff n x).1 hx
  have e : ((a * ((l : ℕ) : unitBall l u ρ) ^ n : unitBall l u ρ) : Disc l u ρ) =
      (l : Disc l u ρ) ^ n * (a : Disc l u ρ) := by
    push_cast; ring
  rw [e, norm_pow_mul hmul]
  calc ((l : ℝ)⁻¹) ^ n * ‖(a : Disc l u ρ)‖ ≤ ((l : ℝ)⁻¹) ^ n * 1 :=
        mul_le_mul_of_nonneg_left (norm_le_one_of_mem a) (inv_pow_pos n).le
    _ = _ := mul_one _

theorem tendsto_inv_pow : Tendsto (fun n : ℕ => ((l : ℝ)⁻¹) ^ n) atTop (𝓝 0) := by
  have h1 : (1 : ℝ) < l := Nat.one_lt_cast.2 hl.out.one_lt
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 (by linarith)) (inv_lt_one_of_one_lt₀ h1)

theorem isAdicComplete_unitBall (hmul : ∀ y : Disc l u ρ, ‖(l : Disc l u ρ) * y‖ = (l : ℝ)⁻¹ * ‖y‖) :
    IsAdicComplete (Ideal.span {((l : ℕ) : unitBall l u ρ)}) (unitBall l u ρ) := by
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have hb : ∀ n : ℕ, ‖(x : Disc l u ρ)‖ ≤ ((l : ℝ)⁻¹) ^ n := fun n =>
      norm_le_of_mem hmul n x (by simpa [SModEq.sub_mem] using hx n)
    have h0 : ‖(x : Disc l u ρ)‖ ≤ 0 := ge_of_tendsto' tendsto_inv_pow hb
    exact Subtype.ext (by simpa using norm_le_zero_iff.1 h0)
  · intro f hf

    have hd : ∀ m n, m ≤ n → ‖((f m : Disc l u ρ) - f n)‖ ≤ ((l : ℝ)⁻¹) ^ m := fun m n hmn => by
      have := norm_le_of_mem hmul m (f m - f n) (SModEq.sub_mem.1 (hf hmn))
      simpa using this
    have hc : CauchySeq (fun n => (f n : Disc l u ρ)) := by
      refine cauchySeq_of_le_tendsto_0 (fun N => 2 * ((l : ℝ)⁻¹) ^ N) (fun n m N hn hm => ?_) ?_
      · rw [dist_eq_norm]
        have e : (f n : Disc l u ρ) - f m = ((f N : Disc l u ρ) - f m) - ((f N : Disc l u ρ) - f n) := by ring
        rw [e]
        refine (norm_sub_le _ _).trans ?_
        linarith [hd N m hm, hd N n hn]
      · simpa using tendsto_inv_pow.const_mul (2 : ℝ)
    obtain ⟨L₀, hL⟩ := cauchySeq_tendsto_of_complete hc
    have hL1 : ‖L₀‖ ≤ 1 :=
      (isClosed_le continuous_norm continuous_const).mem_of_tendsto hL
        (Eventually.of_forall fun n => norm_le_one_of_mem (f n))
    let L : unitBall l u ρ := ⟨L₀, hL1⟩
    refine ⟨L, fun n => ?_⟩
    rw [SModEq.sub_mem, mem_smul_top_iff]
    have hn : ‖(f n : Disc l u ρ) - L₀‖ ≤ ((l : ℝ)⁻¹) ^ n := by
      have ht : Tendsto (fun k => (f n : Disc l u ρ) - f k) atTop (𝓝 ((f n : Disc l u ρ) - L₀)) :=
        tendsto_const_nhds.sub hL
      exact (isClosed_le continuous_norm continuous_const).mem_of_tendsto ht
        (eventually_atTop.2 ⟨n, fun k hk => hd n k hk⟩)
    let v : (Disc l u ρ)ˣ := (isUnit_l_disc l u ρ).unit
    have hv : (v : Disc l u ρ) = (l : Disc l u ρ) := (isUnit_l_disc l u ρ).unit_spec
    set y : Disc l u ρ := ((v⁻¹ ^ n : (Disc l u ρ)ˣ) : Disc l u ρ) * ((f n : Disc l u ρ) - L₀) with hy
    have hly : (l : Disc l u ρ) ^ n * y = (f n : Disc l u ρ) - L₀ := by
      rw [hy, ← mul_assoc, ← hv, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel,
        one_pow, Units.val_one, one_mul]
    have hy1 : ‖y‖ ≤ 1 := by
      have h2 : ((l : ℝ)⁻¹) ^ n * ‖y‖ ≤ ((l : ℝ)⁻¹) ^ n * 1 := by
        rw [← norm_pow_mul hmul, hly, mul_one]; exact hn
      exact le_of_mul_le_mul_left h2 (inv_pow_pos n)
    refine ⟨⟨y, hy1⟩, Subtype.ext ?_⟩
    push_cast
    rw [mul_comm]
    exact hly

end UnitBall

theorem isAdicComplete_unitBall (hL : ∀ y : Disc l u ρ, ‖(l : Disc l u ρ) * y‖ = (l : ℝ)⁻¹ * ‖y‖) :
    IsAdicComplete (Ideal.span {(l : unitBall l u ρ)}) (unitBall l u ρ) :=
  UnitBall.isAdicComplete_unitBall hL

end Complete

section Main

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

def locMap : Per.AinfP l →+* bk.DA bk.ρ₀ :=
  IsLocalization.Away.lift (l : Ainf l) (g := bk.iA) (by rw [map_natCast]; exact isUnit_l_disc _ _ _)

theorem locMap_alg (a : Ainf l) : locMap bk (algebraMap (Ainf l) (Per.AinfP l) a) = bk.iA a :=
  IsLocalization.Away.lift_eq _ _ a

variable {bk}

theorem le_norm_mul_coprime (hL : ∀ y : bk.DA bk.ρ₀, ‖(l : bk.DA bk.ρ₀) * y‖ = (l : ℝ)⁻¹ * ‖y‖)
    {m : ℕ} (hm : ¬ l ∣ m) (w : bk.DA bk.ρ₀) : ‖w‖ ≤ ‖(m : bk.DA bk.ρ₀) * w‖ := by
  have hcop : IsCoprime (m : ℤ) (l : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hm).symm
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : ((a : ℤ) : bk.DA bk.ρ₀) * m + (b : bk.DA bk.ρ₀) * l = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → bk.DA bk.ρ₀) hab
  have hn : ∀ c : ℤ, ‖(c : bk.DA bk.ρ₀)‖ ≤ 1 := fun c => by
    simpa using norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) (c : Ainf l)
  have e : w = (a : bk.DA bk.ρ₀) * ((m : bk.DA bk.ρ₀) * w) + (b : bk.DA bk.ρ₀) * ((l : bk.DA bk.ρ₀) * w) := by
    linear_combination (-w) * h1
  have h2 : ‖w‖ ≤ max ‖(m : bk.DA bk.ρ₀) * w‖ ((l : ℝ)⁻¹ * ‖w‖) := by
    conv_lhs => rw [e]
    refine (norm_add_le_max_disc _ _).trans (max_le_max ?_ ?_)
    · exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (hn a))
    · rw [← hL]; exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (hn b))
  rcases le_max_iff.1 h2 with h | h
  · exact h
  · have : ‖w‖ ≤ 0 := by nlinarith [inv_l_lt_one (l := l), norm_nonneg w]
    exact this.trans (norm_nonneg _)

theorem norm_locMap_gen (hL : ∀ y : bk.DA bk.ρ₀, ‖(l : bk.DA bk.ρ₀) * y‖ = (l : ℝ)⁻¹ * ‖y‖)
    (hθ : ∀ a : Ainf l, Per.θ l a = 0 → ‖bk.iA a‖ ≤ (l : ℝ)⁻¹)
    (y : Per.AinfP l) (x : Ainf l) (hx : Per.θ l x = 0) (n : ℕ)
    (hn : ((n.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Ainf l) (Per.AinfP l) x ^ n) : ‖locMap bk y‖ ≤ 1 := by
  have h1 := congrArg (locMap bk) hn
  rw [map_mul, map_natCast, map_pow, locMap_alg] at h1
  have hxn' : ∀ k : ℕ, ‖bk.iA x ^ k‖ ≤ (l : ℝ)⁻¹ ^ k := by
    intro n
    induction n with
    | zero => simpa using norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) (1 : Ainf l)
    | succ k ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul ih (hθ x hx) (norm_nonneg _) (by positivity))
  have hxn := hxn' n
  set v := n.factorial.factorization l
  set m := n.factorial / l ^ v
  have hfac : (n.factorial : bk.DA bk.ρ₀) = (l : bk.DA bk.ρ₀) ^ v * (m : bk.DA bk.ρ₀) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → bk.DA bk.ρ₀) (Nat.ordProj_mul_ordCompl_eq_self n.factorial l).symm
  have hm : ¬ l ∣ m := Nat.not_dvd_ordCompl hl.out (Nat.factorial_ne_zero n)
  have hv : v ≤ n := (Nat.factorization_factorial_le_div_pred hl.out n).trans (Nat.div_le_self _ _)
  rw [hfac, mul_assoc] at h1
  replace h1 := congrArg norm h1
  rw [norm_lpow_mul hL] at h1
  have h2 := le_norm_mul_coprime hL hm (locMap bk y)
  have hpos : (0 : ℝ) < (l : ℝ)⁻¹ ^ v := by
    have : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
    positivity
  have h3 : (l : ℝ)⁻¹ ^ v * ‖locMap bk y‖ ≤ (l : ℝ)⁻¹ ^ v * 1 := by
    calc (l : ℝ)⁻¹ ^ v * ‖locMap bk y‖ ≤ (l : ℝ)⁻¹ ^ v * ‖(m : bk.DA bk.ρ₀) * locMap bk y‖ :=
          mul_le_mul_of_nonneg_left h2 hpos.le
      _ = ‖bk.iA x ^ n‖ := h1
      _ ≤ (l : ℝ)⁻¹ ^ n := hxn
      _ = (l : ℝ)⁻¹ ^ v * (l : ℝ)⁻¹ ^ (n - v) := by rw [← pow_add, Nat.add_sub_cancel' hv]
      _ ≤ (l : ℝ)⁻¹ ^ v * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity) inv_l_lt_one.le) hpos.le
  exact le_of_mul_le_mul_left h3 hpos

theorem norm_locMap_acris0 (hL : ∀ y : bk.DA bk.ρ₀, ‖(l : bk.DA bk.ρ₀) * y‖ = (l : ℝ)⁻¹ * ‖y‖)
    (hθ : ∀ a : Ainf l, Per.θ l a = 0 → ‖bk.iA a‖ ≤ (l : ℝ)⁻¹)
    (y : Per.AinfP l) (hy : y ∈ Per.Acris0 l) : ‖locMap bk y‖ ≤ 1 := by
  let S : Subalgebra (Ainf l) (Per.AinfP l) :=
    { carrier := {y | ‖locMap bk y‖ ≤ 1}
      mul_mem' := fun {x y} a b => by
        change ‖locMap bk (x * y)‖ ≤ 1
        rw [map_mul]; exact (norm_mul_le _ _).trans (mul_le_one₀ a (norm_nonneg _) b)
      add_mem' := fun {x y} a b => by
        change ‖locMap bk (x + y)‖ ≤ 1
        rw [map_add]; exact (norm_add_le_max_disc _ _).trans (max_le a b)
      algebraMap_mem' := fun r => by
        change ‖locMap bk (algebraMap (Ainf l) (Per.AinfP l) r)‖ ≤ 1
        rw [locMap_alg]; exact norm_toDisc_le r }
  exact GlobalTheory.RingIface.Acris0_le_of_dividedPowers l S (fun x n y hx hn => norm_locMap_gen hL hθ y x hx n hn) hy

end Main

section Ext

theorem exists_acris_to_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    ∃ γ : Per.Acris l →+* bk.DA bk.ρ₀,
      (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) ∧ ∀ x, ‖γ x‖ ≤ 1 := by
  intro l _ K bk
  obtain ⟨-, hL, hθ⟩ := GlobalTheory.T.breuilKisin_seedDisc_norm_bounds l K bk
  let B := unitBall l (bk.ev X) bk.ρ₀
  haveI : IsAdicComplete (Ideal.span {(l : B)}) B := isAdicComplete_unitBall hL
  let f0 : Per.Acris0 l →+* B :=
    ((locMap bk).comp (Per.Acris0 l).val.toRingHom).codRestrict B
      (fun y => norm_locMap_acris0 hL hθ y y.2)
  have hbij : Function.Bijective (algebraMap B (GlobalTheory.AdicMaps.PHat l B)) := by
    have : ⇑(algebraMap B (GlobalTheory.AdicMaps.PHat l B)) = ⇑(AdicCompletion.of (Ideal.span {(l : B)}) B) := by
      funext b; rw [AdicCompletion.algebraMap_apply]; rfl
    rw [this]; exact AdicCompletion.of_bijective _ _
  let e := RingEquiv.ofBijective (algebraMap B (GlobalTheory.AdicMaps.PHat l B)) hbij
  obtain ⟨c, hc⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
  let γ : Per.Acris l →+* bk.DA bk.ρ₀ :=
    B.subtype.comp (e.symm.toRingHom.comp ((GlobalTheory.AdicMaps.padicMap l f0).comp c.toRingHom))
  refine ⟨γ, fun a => ?_, fun x => (e.symm (GlobalTheory.AdicMaps.padicMap l f0 (c x))).2⟩
  have h1 : GlobalTheory.AdicMaps.padicMap l f0 (c (algebraMap (Ainf l) (Per.Acris l) a)) =
      algebraMap B (GlobalTheory.AdicMaps.PHat l B) (f0 (algebraMap (Ainf l) (Per.Acris0 l) a)) := by
    rw [GlobalTheory.RingIface.tower, hc]
    exact GlobalTheory.AdicMaps.padicMap_alg l f0 _
  show ((e.symm (GlobalTheory.AdicMaps.padicMap l f0 (c (algebraMap (Ainf l) (Per.Acris l) a))) : B) : bk.DA bk.ρ₀) = bk.iA a
  rw [h1]
  have h2 : e.symm (algebraMap B (GlobalTheory.AdicMaps.PHat l B) (f0 (algebraMap (Ainf l) (Per.Acris0 l) a))) =
      f0 (algebraMap (Ainf l) (Per.Acris0 l) a) := e.symm_apply_apply _
  rw [h2]
  exact locMap_alg bk a

end Ext

end GlobalTheory.AcrisDisc
