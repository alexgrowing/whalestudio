import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscSer

variable (l : ℕ) {W : Type} [CommRing W] (ρ : ℝ≥0)

theorem isUnit_l : IsUnit (l : (PreDisc l (0 : W) 1)⟦X⟧) := by
  rw [← map_natCast (C : PreDisc l (0 : W) 1 →+* (PreDisc l (0 : W) 1)⟦X⟧)]
  refine IsUnit.map _ ?_
  rw [← map_natCast (algebraMap W (PreDisc l (0 : W) 1))]
  exact IsLocalization.Away.algebraMap_isUnit _

def phi : PreDisc l (X : W⟦X⟧) ρ →+* (PreDisc l (0 : W) 1)⟦X⟧ :=
  IsLocalization.Away.lift (l : W⟦X⟧) (g := PowerSeries.map (algebraMap W (PreDisc l (0 : W) 1))) (by
    rw [map_natCast]; exact isUnit_l l)

theorem phi_alg (s : W⟦X⟧) :
    phi l ρ (algebraMap W⟦X⟧ (PreDisc l (X : W⟦X⟧) ρ) s) = PowerSeries.map (algebraMap W (PreDisc l (0 : W) 1)) s :=
  IsLocalization.Away.lift_eq _ _ s

theorem phi_inv :
    phi l ρ (IsLocalization.Away.invSelf (l : W⟦X⟧)) = C (IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W)) := by
  have h := congrArg (phi l ρ) (IsLocalization.Away.mul_invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧))
  rw [map_mul, phi_alg, map_natCast, map_one] at h
  have h2 : (l : (PreDisc l (0 : W) 1)⟦X⟧) * C (IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W)) = 1 := by
    rw [← map_natCast (C : PreDisc l (0 : W) 1 →+* (PreDisc l (0 : W) 1)⟦X⟧), ← map_mul,
      ← map_natCast (algebraMap W (PreDisc l (0 : W) 1)), IsLocalization.Away.mul_invSelf, map_one]
  exact (isUnit_l l).mul_left_cancel (h.trans h2.symm)

def aPre (n : ℕ) : PreDisc l (X : W⟦X⟧) ρ →+ PreDisc l (0 : W) 1 :=
  (coeff n : (PreDisc l (0 : W) 1)⟦X⟧ →ₗ[PreDisc l (0 : W) 1] PreDisc l (0 : W) 1).toAddMonoidHom.comp
    (phi l ρ).toAddMonoidHom

theorem aPre_apply (n : ℕ) (y : PreDisc l (X : W⟦X⟧) ρ) : aPre l ρ n y = coeff n (phi l ρ y) := rfl

theorem aPre_mono (n a b c : ℕ) :
    aPre l ρ n (algebraMap W⟦X⟧ (PreDisc l (X : W⟦X⟧) ρ) ((l : W⟦X⟧) ^ a * X ^ b) *
      IsLocalization.Away.invSelf (l : W⟦X⟧) ^ c) =
    if n = b then algebraMap W (PreDisc l (0 : W) 1) ((l : W) ^ a) *
      IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c else 0 := by
  rw [aPre_apply, map_mul, phi_alg, map_pow, phi_inv]
  have e : PowerSeries.map (algebraMap W (PreDisc l (0 : W) 1)) ((l : W⟦X⟧) ^ a * X ^ b) *
      C (IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W)) ^ c =
      C (algebraMap W (PreDisc l (0 : W) 1) ((l : W) ^ a) *
        IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c) * X ^ b := by
    simp only [map_mul, map_pow, map_natCast, map_X]; ring
  rw [e, coeff_C_mul_X_pow]

theorem norm_W_mono (hl : 0 < l) (a c : ℕ) :
    ‖algebraMap W (PreDisc l (0 : W) 1) ((l : W) ^ a) *
      IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c‖ ≤ (l : ℝ) ^ c / (l : ℝ) ^ a := by
  have hl' : (0 : ℝ) < l := Nat.cast_pos.2 hl
  exact gauge_le l (0 : W) 1 (by positivity) (Submodule.subset_span ⟨a, 0, c, by field_simp; simp, by simp⟩)

theorem norm_aPre_le (hl : 0 < l) (hρ : ρ ≤ 1) (y : PreDisc l (X : W⟦X⟧) ρ) (n : ℕ) :
    ‖aPre l ρ n y‖ * (ρ : ℝ) ^ n ≤ ‖y‖ := by
  suffices h : ∀ r : ℝ, 0 < r → y ∈ ball l (X : W⟦X⟧) ρ r → ∀ n, ‖aPre l ρ n y‖ * (ρ : ℝ) ^ n ≤ r from
    le_of_forall_gt_imp_ge_of_dense fun r hr =>
      h r ((norm_nonneg y).trans_lt hr) (mem_ball_of_gauge_lt l _ ρ hr) n
  have hρ' : (ρ : ℝ) ≤ 1 := by exact_mod_cast hρ
  have hl' : (0 : ℝ) < l := Nat.cast_pos.2 hl
  have hadd : ∀ (r : ℝ) (n : ℕ) (z w : PreDisc l (0 : W) 1), ‖z‖ * (ρ : ℝ) ^ n ≤ r → ‖w‖ * (ρ : ℝ) ^ n ≤ r →
      ‖z + w‖ * (ρ : ℝ) ^ n ≤ r := fun r n z w hz hw =>
    (mul_le_mul_of_nonneg_right (gauge_add_le_max l (0 : W) 1 z w) (by positivity)).trans
      (by rw [max_mul_of_nonneg _ _ (by positivity)]; exact max_le hz hw)
  intro r hr hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, c, h1, rfl⟩ := hx
    intro n
    rw [aPre_mono]
    split_ifs with hn
    · subst hn
      calc _ ≤ (l : ℝ) ^ c / (l : ℝ) ^ a * (ρ : ℝ) ^ n :=
            mul_le_mul_of_nonneg_right (norm_W_mono l hl a c) (by positivity)
        _ ≤ r := by rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; exact h1
    · rw [norm_zero, zero_mul]; exact hr.le
  | zero => intro n; rw [map_zero, norm_zero, zero_mul]; exact hr.le
  | add x y _ _ hx hy => intro n; rw [map_add]; exact hadd r n _ _ (hx n) (hy n)
  | smul s x _ hx =>
    intro n
    rw [aPre_apply, Algebra.smul_def, map_mul, phi_alg, coeff_mul]
    refine Finset.sum_induction _ (fun z => ‖z‖ * (ρ : ℝ) ^ n ≤ r) (fun z w hz hw => hadd r n z w hz hw)
      (by rw [norm_zero, zero_mul]; exact hr.le) (fun p hp => ?_)
    have hp2 : p.2 ≤ n := by have := _root_.Finset.HasAntidiagonal.mem_antidiagonal.1 hp; omega
    rw [coeff_map]
    calc ‖algebraMap W (PreDisc l (0 : W) 1) (coeff p.1 s) * coeff p.2 (phi l ρ x)‖ * (ρ : ℝ) ^ n
        ≤ (1 * ‖coeff p.2 (phi l ρ x)‖) * (ρ : ℝ) ^ p.2 :=
          mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            (norm_algebraMap_le (l := l) (u := (0 : W)) (ρ := 1) _) (norm_nonneg _)))
            (pow_le_pow_of_le_one (by positivity) hρ' hp2) (by positivity) (by positivity)
      _ ≤ r := by rw [one_mul]; exact hx p.2

theorem norm_X_pow_le (hρ0 : 0 < ρ) (m : ℕ) :
    ‖algebraMap W⟦X⟧ (PreDisc l (X : W⟦X⟧) ρ) (X ^ m)‖ ≤ (ρ : ℝ) ^ m := by
  have := norm_toDisc_pow_le (l := l) (u := (X : W⟦X⟧)) (ρ := ρ) m hρ0
  rwa [toDisc, RingHom.comp_apply, norm_ofPre] at this

theorem norm_le_of_aPre [Fact l.Prime] (hρ0 : 0 < ρ) (hρ : ρ < 1) (y : PreDisc l (X : W⟦X⟧) ρ) (r : ℝ)
    (hr : 0 ≤ r) (h : ∀ n, ‖aPre l ρ n y‖ * (ρ : ℝ) ^ n ≤ r) : ‖y‖ ≤ r := by
  have hl : (0 : ℝ) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
  obtain ⟨c, s, hs⟩ := IsLocalization.Away.surj (l : W⟦X⟧) y
  have hy : y = algebraMap _ _ s * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c := by
    rw [← hs, mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]
  have hco : ∀ n, aPre l ρ n y =
      algebraMap W (PreDisc l (0 : W) 1) (coeff n s) * IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c := by
    intro n
    rw [hy, aPre_apply, map_mul, phi_alg, map_pow, phi_inv, ← map_pow, coeff_mul_C, coeff_map]
  refine le_of_forall_gt_imp_ge_of_dense fun t ht => ?_
  have ht0 : 0 < t := hr.trans_lt ht
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos ht0 (pow_pos hl c)) (show (ρ : ℝ) < 1 by exact_mod_cast hρ)
  set hd : W⟦X⟧ := ∑ m ∈ Finset.range N, C (coeff m s) * X ^ m with hhd
  obtain ⟨s', hs'⟩ : (X : W⟦X⟧) ^ N ∣ s - hd := X_pow_dvd_iff.2 fun m hm => by
    simp [hhd, map_sub, coeff_C_mul_X_pow, map_sum, Finset.mem_range, hm]
  have hsplit : y = ∑ m ∈ Finset.range N, algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (C (coeff m s) * X ^ m) *
        IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c +
      algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X ^ N * s') *
        IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c := by
    rw [hy, ← Finset.sum_mul, ← map_sum, ← add_mul, ← map_add, ← hs', ← hhd, add_sub_cancel]
  rw [hsplit]
  refine (gauge_add_le_max l _ ρ _ _).trans (max_le ?_ ?_)
  · refine Finset.sum_induction _ (fun z => ‖z‖ ≤ t)
      (fun a b ha hb => (gauge_add_le_max l _ ρ a b).trans (max_le ha hb)) (by rw [norm_zero]; exact ht0.le)
      fun m _ => ?_
    have e : algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (C (coeff m s) * X ^ m) *
        IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c =
        preMap l (0 : W) 1 (X : W⟦X⟧) ρ C (algebraMap W _ (coeff m s) *
          IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c) *
          algebraMap W⟦X⟧ (PreDisc l (X : W⟦X⟧) ρ) (X ^ m) := by
      rw [map_mul (preMap l (0 : W) 1 (X : W⟦X⟧) ρ C), map_pow (preMap l (0 : W) 1 (X : W⟦X⟧) ρ C), preMap_alg, preMap_inv,
        map_mul (algebraMap W⟦X⟧ (PreDisc l (X : W⟦X⟧) ρ))]; ring
    rw [e]
    have hpm := norm_preMap_le (l := l) (u := (0 : W)) (ρ := 1) (u' := (X : W⟦X⟧)) (ρ' := ρ) C (by simp)
      (algebraMap W _ (coeff m s) * IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c)
    refine (norm_mul_le _ _).trans ((mul_le_mul hpm (norm_X_pow_le l ρ hρ0 m) (norm_nonneg _)
      (norm_nonneg _)).trans ?_)
    rw [← hco]; exact (h m).trans ht.le
  · have e : algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X ^ N * s') *
        IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c =
        s' • (algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) ((l : W⟦X⟧) ^ 0 * X ^ N) *
          IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c) := by
      rw [Algebra.smul_def, pow_zero, one_mul, mul_comm ((X : W⟦X⟧) ^ N) s', map_mul, mul_assoc]
    rw [e]
    refine gauge_le l _ ρ ht0 (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, N, c, ?_, rfl⟩))
    rw [lt_div_iff₀ (by positivity)] at hN
    rw [pow_zero, mul_one, mul_comm]; exact hN.le

theorem continuous_aPre (hl : 0 < l) (hρ0 : 0 < ρ) (hρ : ρ ≤ 1) (n : ℕ) : Continuous (aPre l ρ n (W := W)) :=
  AddMonoidHomClass.continuous_of_bound _ ((ρ : ℝ) ^ n)⁻¹ fun y => by
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]; exact norm_aPre_le l ρ hl hρ y n

theorem norm_aPre_le_const (hl : 0 < l) (y : PreDisc l (X : W⟦X⟧) ρ) :
    ∃ C : ℝ, ∀ n, ‖aPre l ρ n y‖ ≤ C := by
  obtain ⟨c, s, hs⟩ := IsLocalization.Away.surj (l : W⟦X⟧) y
  have hy : y = algebraMap _ _ s * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c := by
    rw [← hs, mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]
  refine ⟨(l : ℝ) ^ c / (l : ℝ) ^ 0, fun n => ?_⟩
  rw [hy, aPre_apply, map_mul, phi_alg, map_pow, phi_inv, ← map_pow, coeff_mul_C, coeff_map]
  refine (norm_mul_le _ _).trans ((mul_le_mul (norm_algebraMap_le (l := l) (u := (0 : W)) (ρ := 1) _)
    le_rfl (norm_nonneg _) zero_le_one).trans ?_)
  rw [one_mul]
  have := norm_W_mono (W := W) l hl 0 c
  rwa [pow_zero, map_one, one_mul] at this

theorem exists_coeff_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 →
    ∃ a : ℕ → (bk.DS ρ →+ Disc l (0 : Wq l bk.a) 1),
      (∀ n x, a n (toDisc l (X : bk.S) ρ x) = toDisc l (0 : Wq l bk.a) 1 (coeff n x)) ∧
      (∀ n y, ‖a n y‖ * (ρ : ℝ) ^ n ≤ ‖y‖) ∧
      (∀ y (r : ℝ), 0 ≤ r → (∀ n, ‖a n y‖ * (ρ : ℝ) ^ n ≤ r) → ‖y‖ ≤ r) ∧
      ∀ y, Filter.Tendsto (fun n => ‖a n y‖ * (ρ : ℝ) ^ n) Filter.atTop (nhds 0) := by
  intro l _ K bk ρ hρ0 hρ1
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hl' : (0 : ℝ) < l := Nat.cast_pos.2 hl
  have hc := fun n => continuous_aPre l (W := Wq l bk.a) ρ hl hρ0 hρ1.le n
  let A : ℕ → (bk.DS ρ →+ Disc l (0 : Wq l bk.a) 1) := fun n => (aPre l ρ n).completion (hc n)
  have hA : ∀ n y, A n (ofPre l (X : bk.S) ρ y) = ofPre l (0 : Wq l bk.a) 1 (aPre l ρ n y) := fun n y =>
    AddMonoidHom.completion_coe _ _ y
  have hAc : ∀ n, Continuous (A n) := fun n => AddMonoidHom.continuous_completion _ _
  have h2 : ∀ n y, ‖A n y‖ * (ρ : ℝ) ^ n ≤ ‖y‖ := by
    intro n y
    refine (denseRange_ofPre l (X : bk.S) ρ).induction_on y
      (isClosed_le (((hAc n).norm).mul continuous_const) continuous_norm) fun y => ?_
    rw [hA, norm_ofPre, norm_ofPre]
    exact norm_aPre_le l ρ hl hρ1.le y n
  refine ⟨A, fun n x => ?_, h2, fun y r hr h => ?_, fun y => ?_⟩
  · change A n (ofPre l (X : bk.S) ρ (algebraMap _ _ x)) = ofPre l (0 : Wq l bk.a) 1 (algebraMap _ _ (coeff n x))
    rw [hA, aPre_apply, phi_alg, coeff_map]
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨z, hz⟩ := (denseRange_ofPre l (X : bk.S) ρ).exists_dist_lt y (half_pos hε)
    rw [dist_eq_norm] at hz
    have hz' : ‖z‖ ≤ r + ε / 2 := by
      refine norm_le_of_aPre l ρ hρ0 hρ1 z _ (by positivity) fun n => ?_
      rw [show ‖aPre l ρ n z‖ = ‖ofPre l (0 : Wq l bk.a) 1 (aPre l ρ n z)‖ from (norm_ofPre l (0 : Wq l bk.a) 1 _).symm, show ofPre l (0 : Wq l bk.a) 1 (aPre l ρ n z) =
        A n y - A n (y - ofPre l (X : bk.S) ρ z) by rw [map_sub, sub_sub_cancel, hA]]
      refine (mul_le_mul_of_nonneg_right (norm_sub_le _ _) (by positivity)).trans ?_
      rw [add_mul]
      exact add_le_add (h n) ((h2 n _).trans hz.le)
    calc ‖y‖ ≤ ‖y - ofPre l (X : bk.S) ρ z‖ + ‖ofPre l (X : bk.S) ρ z‖ := norm_le_norm_sub_add _ _
      _ ≤ ε / 2 + (r + ε / 2) := add_le_add hz.le (by rw [norm_ofPre]; exact hz')
      _ = r + ε := by ring
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨z, hz⟩ := (denseRange_ofPre l (X : bk.S) ρ).exists_dist_lt y (half_pos hε)
    rw [dist_eq_norm] at hz
    obtain ⟨C, hC⟩ := norm_aPre_le_const l ρ hl z
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos (half_pos hε) (show (0 : ℝ) < C + 1 by linarith))
      (show (ρ : ℝ) < 1 by exact_mod_cast hρ1)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
    have hρn : (ρ : ℝ) ^ n ≤ (ρ : ℝ) ^ N := pow_le_pow_of_le_one (by positivity) (by exact_mod_cast hρ1.le) hn
    rw [lt_div_iff₀ (by linarith)] at hN
    have e : A n y = A n (y - ofPre l (X : bk.S) ρ z) + ofPre l (0 : Wq l bk.a) 1 (aPre l ρ n z) := by
      rw [← hA, ← map_add, sub_add_cancel]
    rw [e]
    calc ‖A n (y - ofPre l (X : bk.S) ρ z) + ofPre l (0 : Wq l bk.a) 1 (aPre l ρ n z)‖ * (ρ : ℝ) ^ n
        ≤ (‖A n (y - ofPre l (X : bk.S) ρ z)‖ + ‖aPre l ρ n z‖) * (ρ : ℝ) ^ n := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [show ‖aPre l ρ n z‖ = ‖ofPre l (0 : Wq l bk.a) 1 (aPre l ρ n z)‖ from (norm_ofPre l (0 : Wq l bk.a) 1 _).symm]
          exact norm_add_le _ _
      _ = ‖A n (y - ofPre l (X : bk.S) ρ z)‖ * (ρ : ℝ) ^ n + ‖aPre l ρ n z‖ * (ρ : ℝ) ^ n := add_mul _ _ _
      _ ≤ ‖y - ofPre l (X : bk.S) ρ z‖ + C * (ρ : ℝ) ^ N :=
          add_le_add (h2 n _) (mul_le_mul (hC n) hρn (by positivity) hC0)
      _ < ε / 2 + ε / 2 := by
          refine add_lt_add_of_lt_of_le hz ?_
          nlinarith [pow_nonneg (show (0 : ℝ) ≤ ρ by positivity) N]
      _ = ε := add_halves ε

end GlobalTheory.BSP.DiscSer
