import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionBasicPropertiesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscZero

variable {l : ℕ} [hl : Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l]

local notation "𝕎k" => WittVector l k
local notation "Pk" => PreDisc l (0 : WittVector l k) 1
local notation "Dk" => Disc l (0 : WittVector l k) 1
local notation "sI" => IsLocalization.Away.invSelf (S := PreDisc l (0 : WittVector l k) 1) (l : WittVector l k)

omit [Field k] [CharP k l] [PerfectRing k l] in
theorem l_pos : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos

omit [Field k] [CharP k l] [PerfectRing k l] in
theorem one_lt_l : (1 : ℝ) < l := Nat.one_lt_cast.2 hl.out.one_lt

omit [CharP k l] [PerfectRing k l] in
theorem l_mul_inv : (l : Pk) * sI = 1 := by
  rw [← map_natCast (algebraMap (𝕎k) (Pk)) l]
  exact IsLocalization.Away.mul_invSelf _

omit [CharP k l] [PerfectRing k l] in

theorem norm_l_mul (y : Pk) : ‖(l : Pk) * y‖ = ‖y‖ / l := by
  have h := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l (WittVector l k) 0 1).2.1 (ofPre l 0 1 y)
  rw [← map_natCast (ofPre l (0 : WittVector l k) 1) l, ← map_mul, norm_ofPre, norm_ofPre] at h
  exact h

omit [CharP k l] [PerfectRing k l] in
theorem norm_l_pow_mul (m : ℕ) (y : Pk) : ‖(l : Pk) ^ m * y‖ = ‖y‖ / (l : ℝ) ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', mul_assoc, norm_l_mul, ih]; ring

omit [CharP k l] [PerfectRing k l] in
theorem norm_inv_pow_mul (n : ℕ) (y : Pk) : ‖sI ^ n * y‖ = ‖y‖ * (l : ℝ) ^ n := by
  have h := norm_l_pow_mul n (sI ^ n * y)
  rw [← mul_assoc, ← mul_pow, l_mul_inv, one_pow, one_mul] at h
  rw [h, div_mul_cancel₀ _ (pow_ne_zero _ l_pos.ne')]

omit [PerfectRing k l] in
theorem algebraMap_injective : Function.Injective (algebraMap (𝕎k) (Pk)) := by
  refine IsLocalization.injective (M := Submonoid.powers (l : 𝕎k)) (Pk) ?_
  refine powers_le_nonZeroDivisors_of_noZeroDivisors ?_
  intro h
  have := congrArg (fun x : 𝕎k => x.coeff 1) h
  simp [WittVector.coeff_p_one] at this

theorem ball_lt_one {r : ℝ} (hr : r < 1) {y : Pk} (hy : y ∈ ball l (0 : 𝕎k) 1 r) :
    ∃ w : 𝕎k, y = algebraMap (𝕎k) (Pk) ((l : 𝕎k) * w) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, c, h1, rfl⟩ := hx
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · have hca : c < a := by
        have h2 : (l : ℝ) ^ c < (l : ℝ) ^ a := by
          simp only [NNReal.coe_one, one_pow, mul_one] at h1
          calc (l : ℝ) ^ c ≤ r * (l : ℝ) ^ a := h1
            _ < 1 * (l : ℝ) ^ a := mul_lt_mul_of_pos_right hr (pow_pos l_pos a)
            _ = _ := one_mul _
        exact (pow_lt_pow_iff_right₀ one_lt_l).1 h2
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hca
      refine ⟨(l : 𝕎k) ^ d, ?_⟩
      simp only [pow_zero, mul_one, map_mul, map_pow, map_natCast]
      calc (l : Pk) ^ (c + d + 1) * sI ^ c = ((l : Pk) * sI) ^ c * ((l : Pk) * (l : Pk) ^ d) := by ring
        _ = _ := by rw [l_mul_inv, one_pow, one_mul]
    · exact ⟨0, by simp [zero_pow hb.ne']⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨w', rfl⟩ := hy
    exact ⟨w + w', by rw [mul_add, map_add]⟩
  | smul c x _ hx =>
    obtain ⟨w, rfl⟩ := hx
    exact ⟨c * w, by rw [Algebra.smul_def, ← map_mul, mul_left_comm]⟩

theorem norm_alg_unit (v : (𝕎k)ˣ) : ‖algebraMap (𝕎k) (Pk) v‖ = 1 := by
  refine le_antisymm (norm_algebraMap_le _) (not_lt.1 fun h => ?_)
  obtain ⟨r, hr1, hr2⟩ := exists_between h
  obtain ⟨w, hw⟩ := ball_lt_one hr2 (mem_ball_of_gauge_lt l (0 : 𝕎k) 1 hr1)
  have hv : (v : 𝕎k) = (l : 𝕎k) * w := algebraMap_injective hw
  exact (WittVector.irreducible l).not_isUnit (isUnit_of_mul_isUnit_left (hv ▸ v.isUnit))

theorem norm_nf (v : (𝕎k)ˣ) (m n : ℕ) :
    ‖(l : Pk) ^ m * (sI ^ n * algebraMap (𝕎k) (Pk) v)‖ = (l : ℝ) ^ n / (l : ℝ) ^ m := by
  rw [norm_l_pow_mul, norm_inv_pow_mul, norm_alg_unit, one_mul]

theorem norm_alg_pow_mul (v : (𝕎k)ˣ) (m : ℕ) :
    ‖algebraMap (𝕎k) (Pk) ((l : 𝕎k) ^ m * v)‖ = 1 / (l : ℝ) ^ m := by
  rw [map_mul, map_pow, map_natCast, norm_l_pow_mul, norm_alg_unit]

theorem normal_form (y : Pk) (hy : y ≠ 0) :
    ∃ (v : (𝕎k)ˣ) (m n : ℕ), y = (l : Pk) ^ m * (sI ^ n * algebraMap (𝕎k) (Pk) v) := by
  obtain ⟨n, w, h⟩ := IsLocalization.Away.surj (l : 𝕎k) y
  have e : y = sI ^ n * algebraMap (𝕎k) (Pk) w := by
    calc y = y * (algebraMap (𝕎k) (Pk) (l : 𝕎k) * sI) ^ n := by
          rw [IsLocalization.Away.mul_invSelf, one_pow, mul_one]
      _ = sI ^ n * (y * algebraMap (𝕎k) (Pk) (l : 𝕎k) ^ n) := by ring
      _ = _ := by rw [h]
  have hw : w ≠ 0 := by rintro rfl; exact hy (by rw [e, map_zero, mul_zero])
  obtain ⟨m, v, hv⟩ := WittVector.exists_eq_pow_p_mul' w hw
  refine ⟨v, m, n, ?_⟩
  rw [e, hv, map_mul, map_pow, map_natCast]
  ring

theorem norm_mul_pre (x y : Pk) : ‖x * y‖ = ‖x‖ * ‖y‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  obtain ⟨v, m, n, rfl⟩ := normal_form x hx
  obtain ⟨v', m', n', rfl⟩ := normal_form y hy
  have e : (l : Pk) ^ m * (sI ^ n * algebraMap (𝕎k) (Pk) v) *
      ((l : Pk) ^ m' * (sI ^ n' * algebraMap (𝕎k) (Pk) v')) =
      (l : Pk) ^ (m + m') * (sI ^ (n + n') * algebraMap (𝕎k) (Pk) ↑(v * v')) := by
    rw [Units.val_mul, map_mul]; ring
  rw [e, norm_nf, norm_nf, norm_nf, pow_add, pow_add, mul_div_mul_comm]

theorem norm_mul_disc (x y : Dk) : ‖x * y‖ = ‖x‖ * ‖y‖ := by
  refine (denseRange_ofPre l (0 : 𝕎k) 1).induction_on x
    (isClosed_eq (continuous_norm.comp (continuous_id.mul continuous_const))
      (continuous_norm.mul continuous_const)) fun a => ?_
  refine (denseRange_ofPre l (0 : 𝕎k) 1).induction_on y
    (isClosed_eq (continuous_norm.comp (continuous_const.mul continuous_id))
      (continuous_const.mul continuous_norm)) fun b => ?_
  rw [← map_mul, norm_ofPre, norm_ofPre, norm_ofPre]
  exact norm_mul_pre a b

theorem norm_toDisc_unit (w : 𝕎k) (hw : IsUnit w) : ‖toDisc l (0 : 𝕎k) 1 w‖ = 1 := by
  obtain ⟨v, rfl⟩ := hw
  exact (norm_ofPre l (0 : 𝕎k) 1 _).trans (norm_alg_unit v)

theorem toDisc_injective : Function.Injective (toDisc l (0 : 𝕎k) 1) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => by_contra fun hw0 => ?_
  obtain ⟨m, v, rfl⟩ := WittVector.exists_eq_pow_p_mul' w hw0
  have h := (norm_ofPre l (0 : 𝕎k) 1 _).symm.trans (congrArg norm hw)
  rw [norm_zero] at h
  have h2 := norm_alg_pow_mul v m
  rw [norm_preDisc, h] at h2
  exact (one_div_pos.2 (pow_pos l_pos m)).ne h2

theorem mem_range_of_norm_lt (y : Pk) (hy : ‖y‖ < l) : ∃ w : 𝕎k, y = algebraMap (𝕎k) (Pk) w := by
  rcases eq_or_ne y 0 with rfl | hy0
  · exact ⟨0, by simp⟩
  obtain ⟨v, m, n, rfl⟩ := normal_form y hy0
  rw [norm_nf, div_lt_iff₀ (pow_pos l_pos m), ← pow_succ'] at hy
  have hnm : n ≤ m := Nat.lt_succ_iff.1 ((pow_lt_pow_iff_right₀ one_lt_l).1 hy)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  refine ⟨(l : 𝕎k) ^ d * v, ?_⟩
  rw [map_mul, map_pow, map_natCast]
  calc (l : Pk) ^ (n + d) * (sI ^ n * algebraMap (𝕎k) (Pk) v)
      = ((l : Pk) * sI) ^ n * ((l : Pk) ^ d * algebraMap (𝕎k) (Pk) v) := by ring
    _ = _ := by rw [l_mul_inv, one_pow, one_mul]

theorem dvd_of_norm_le (w : 𝕎k) (j : ℕ) (h : ‖algebraMap (𝕎k) (Pk) w‖ ≤ 1 / (l : ℝ) ^ j) :
    (l : 𝕎k) ^ j ∣ w := by
  rcases eq_or_ne w 0 with rfl | hw0
  · exact dvd_zero _
  obtain ⟨m, v, rfl⟩ := WittVector.exists_eq_pow_p_mul' w hw0
  rw [norm_alg_pow_mul, one_div_le_one_div (pow_pos l_pos _) (pow_pos l_pos _),
    pow_le_pow_iff_right₀ one_lt_l] at h
  exact (pow_dvd_pow _ h).mul_right _

omit [CharP k l] [PerfectRing k l] in
theorem norm_alg_l_pow_mul_le (z : 𝕎k) (j : ℕ) :
    ‖algebraMap (𝕎k) (Pk) ((l : 𝕎k) ^ j * z)‖ ≤ 1 / (l : ℝ) ^ j := by
  rw [map_mul, map_pow, map_natCast, norm_l_pow_mul]
  gcongr
  exact norm_algebraMap_le z

omit [CharP k l] [PerfectRing k l] in
theorem norm_ofPre_sub (a b : Pk) : ‖ofPre l (0 : 𝕎k) 1 a - ofPre l (0 : 𝕎k) 1 b‖ = ‖a - b‖ := by
  rw [← map_sub, norm_ofPre]; rfl

theorem exists_of_norm_le (x : Dk) (hx : ‖x‖ ≤ 1) : ∃ w : 𝕎k, x = toDisc l (0 : 𝕎k) 1 w := by
  have hε : ∀ j : ℕ, (0 : ℝ) < 1 / (2 * (l : ℝ) ^ j) := fun j => by have := l_pos (l := l); positivity
  choose y hy using fun j : ℕ => (denseRange_ofPre l (0 : 𝕎k) 1).exists_dist_lt x (hε j)
  simp only [dist_eq_norm] at hy
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.out.two_le
  have hεle : ∀ j : ℕ, 1 / (2 * (l : ℝ) ^ j) ≤ 1 / 2 := fun j => by
    have : (1 : ℝ) ≤ (l : ℝ) ^ j := one_le_pow₀ one_lt_l.le
    gcongr
    linarith
  have hbd : ∀ j, ‖y j‖ < l := fun j => by
    have h1 : ‖ofPre l (0 : 𝕎k) 1 (y j)‖ ≤ ‖x‖ + ‖x - ofPre l (0 : 𝕎k) 1 (y j)‖ := by
      have := norm_sub_le x (x - ofPre l (0 : 𝕎k) 1 (y j))
      rwa [sub_sub_cancel] at this
    rw [norm_ofPre] at h1
    have := hy j
    have := hεle j
    show gauge l (0 : 𝕎k) 1 (y j) < l
    linarith
  choose w hw using fun j => mem_range_of_norm_lt (y j) (hbd j)
  have hcau : ∀ {m n : ℕ}, m ≤ n → (l : 𝕎k) ^ m ∣ w m - w n := fun {m n} hmn => by
    refine dvd_of_norm_le _ m ?_
    have h1 : ‖ofPre l (0 : 𝕎k) 1 (y m) - ofPre l (0 : 𝕎k) 1 (y n)‖ ≤
        ‖x - ofPre l (0 : 𝕎k) 1 (y m)‖ + ‖x - ofPre l (0 : 𝕎k) 1 (y n)‖ := by
      have := norm_sub_le (x - ofPre l (0 : 𝕎k) 1 (y n)) (x - ofPre l (0 : 𝕎k) 1 (y m))
      rw [sub_sub_sub_cancel_left] at this
      linarith
    have e : y m - y n = algebraMap (𝕎k) (Pk) (w m - w n) := by rw [hw m, hw n, map_sub]
    rw [norm_ofPre_sub, e] at h1
    have h2 : 1 / (2 * (l : ℝ) ^ n) ≤ 1 / (2 * (l : ℝ) ^ m) :=
      one_div_le_one_div_of_le (mul_pos two_pos (pow_pos l_pos m))
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one_lt_l.le hmn) zero_le_two)
    have := hy m
    have := hy n
    have h3 : 1 / (2 * (l : ℝ) ^ m) + 1 / (2 * (l : ℝ) ^ m) = 1 / (l : ℝ) ^ m := by
      field_simp; ring
    linarith
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(l : 𝕎k)}) w fun {m n} hmn => by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    exact hcau hmn
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hL
  refine ⟨L, ?_⟩
  have hb : ∀ n : ℕ, ‖toDisc l (0 : 𝕎k) 1 L - x‖ ≤ 2 * (1 / (l : ℝ)) ^ n := fun n => by
    obtain ⟨z, hz⟩ := hL n
    have h1 : ‖toDisc l (0 : 𝕎k) 1 L - x‖ ≤
        ‖toDisc l (0 : 𝕎k) 1 L - ofPre l (0 : 𝕎k) 1 (y n)‖ + ‖x - ofPre l (0 : 𝕎k) 1 (y n)‖ := by
      have := norm_sub_le (toDisc l (0 : 𝕎k) 1 L - ofPre l (0 : 𝕎k) 1 (y n)) (x - ofPre l (0 : 𝕎k) 1 (y n))
      rwa [sub_sub_sub_cancel_right] at this
    have h2 : ‖toDisc l (0 : 𝕎k) 1 L - ofPre l (0 : 𝕎k) 1 (y n)‖ ≤ 1 / (l : ℝ) ^ n := by
      rw [show toDisc l (0 : 𝕎k) 1 L = ofPre l (0 : 𝕎k) 1 (algebraMap (𝕎k) (Pk) L) from rfl,
        norm_ofPre_sub, norm_sub_rev, hw n, ← map_sub, hz]
      exact norm_alg_l_pow_mul_le z n
    have := hy n
    have := hεle n
    have h3 : 1 / (2 * (l : ℝ) ^ n) ≤ 1 / (l : ℝ) ^ n :=
      one_div_le_one_div_of_le (pow_pos l_pos n) (by linarith [pow_pos (l_pos (l := l)) n])
    rw [div_pow, one_pow]
    linarith
  by_contra hne
  have hpos : 0 < ‖toDisc l (0 : 𝕎k) 1 L - x‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne))
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hpos)
    ((div_lt_one (l_pos (l := l))).2 one_lt_l)
  linarith [hb n]

end GlobalTheory.BSP.DiscZero

open GlobalTheory.BSP.DiscZero in

theorem GlobalTheory.BSP.disc_zero_one : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    (∀ x y : Disc l (0 : Wq l bk.a) 1, ‖x * y‖ = ‖x‖ * ‖y‖) ∧
    (∀ x : Disc l (0 : Wq l bk.a) 1, ‖x‖ ≤ 1 → ∃ w, x = toDisc l (0 : Wq l bk.a) 1 w) ∧
    Function.Injective (toDisc l (0 : Wq l bk.a) 1) ∧
    ∀ w : Wq l bk.a, IsUnit w → ‖toDisc l (0 : Wq l bk.a) 1 w‖ = 1 := by
  intro l _ K bk
  exact ⟨norm_mul_disc, exists_of_norm_le, toDisc_injective, norm_toDisc_unit⟩
