import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaFrob
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Polynomial Laurent Filter Topology

section Roots

variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]

theorem norm_le_of_root {q : ℕ} (hq : 2 ≤ q) {c b e t : L} (hc : ‖c‖ = 1)
    (h : c * t ^ q - b * t + e = 0) {Y : ℝ} (hY : 0 ≤ Y) (he : ‖e‖ ≤ Y ^ q)
    (hb : ‖b‖ ≤ Y ^ (q - 1)) : ‖t‖ ≤ Y := by
  by_contra hlt'
  have hlt := not_le.1 hlt'
  have ht0 : 0 < ‖t‖ := hY.trans_lt hlt
  have hq1 : q - 1 ≠ 0 := by omega
  have hpow : Y ^ (q - 1) < ‖t‖ ^ (q - 1) := pow_lt_pow_left₀ hlt hY hq1
  have htq : ‖t‖ ^ q = ‖t‖ ^ (q - 1) * ‖t‖ := by
    rw [← pow_succ]; congr 1; omega
  have h1 : ‖b * t‖ < ‖t‖ ^ q := by
    rw [norm_mul, htq]
    exact mul_lt_mul_of_pos_right (hb.trans_lt hpow) ht0
  have h2 : ‖e‖ < ‖t‖ ^ q := he.trans_lt (pow_lt_pow_left₀ hlt hY (by omega))
  have heq : c * t ^ q = b * t - e := by linear_combination h
  have h3 : ‖c * t ^ q‖ = ‖t‖ ^ q := by rw [norm_mul, hc, one_mul, norm_pow]
  have h4 : ‖b * t - e‖ ≤ max ‖b * t‖ ‖e‖ := by
    have := IsUltrametricDist.norm_add_le_max (b * t) (-e)
    rwa [norm_neg, ← sub_eq_add_neg] at this
  rw [← heq, h3] at h4
  exact absurd h4 (not_le.2 (max_lt h1 h2))

theorem exists_root_of_isAlgClosed [IsAlgClosed L] {q : ℕ} (hq : 2 ≤ q) {c : L} (hc : c ≠ 0)
    (b e : L) : ∃ t : L, c * t ^ q - b * t + e = 0 ∧ (e = 0 → b ≠ 0 → t ≠ 0) := by
  by_cases hbe : e = 0 ∧ b ≠ 0
  · obtain ⟨he, hb⟩ := hbe
    have hdeg : (C c * X ^ (q - 1) - C b).degree ≠ 0 := by
      have : (C c * X ^ (q - 1) - C b).natDegree = q - 1 := by
        compute_degree!
        simp [hc, show q - 1 ≠ 0 by omega]
      rw [Polynomial.degree_eq_natDegree]
      · rw [this]; exact_mod_cast (show q - 1 ≠ 0 by omega)
      · intro h0; rw [h0, natDegree_zero] at this; omega
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_root _ hdeg
    simp only [IsRoot, eval_sub, eval_mul, eval_C, eval_pow, eval_X] at ht
    refine ⟨t, ?_, fun _ _ => ?_⟩
    · have : t ^ q = t ^ (q - 1) * t := by rw [← pow_succ]; congr 1; omega
      rw [he, this]; linear_combination t * ht
    · rintro rfl
      rw [zero_pow (by omega), mul_zero, zero_sub, neg_eq_zero] at ht
      exact hb ht
  · have hdeg : (C c * X ^ q - C b * X + C e).degree ≠ 0 := by
      have : (C c * X ^ q - C b * X + C e).natDegree = q := by
        compute_degree!
        all_goals first | omega | simp [hc, show q ≠ 1 by omega, show q ≠ 0 by omega]
      rw [Polynomial.degree_eq_natDegree]
      · rw [this]; exact_mod_cast (show q ≠ 0 by omega)
      · intro h0; rw [h0, natDegree_zero] at this; omega
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_root _ hdeg
    simp only [IsRoot, eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X] at ht
    exact ⟨t, ht, fun he hb => absurd ⟨he, hb⟩ hbe⟩

end Roots

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem gaussNorm_zcoeff_mono {x : Γ} {σ ρ : ℝ} (hσ0 : 0 < σ) (hσρ : σ ≤ ρ)
    (hx : ConvergesAt (T.zcoeff x) ρ) : gaussNorm (T.zcoeff x) σ ≤ gaussNorm (T.zcoeff x) ρ := by
  refine gaussNorm_le fun n => ?_
  rcases lt_or_ge n 0 with hn | hn
  · rw [T.zcoeff_of_neg _ hn, norm_zero, zero_mul]; exact gaussNorm_nonneg (hσ0.trans_le hσρ)
  · lift n to ℕ using hn
    refine le_trans ?_ (hx.le_gaussNorm n)
    rw [zpow_natCast, zpow_natCast]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hσ0.le hσρ n) (norm_nonneg _)

theorem finSum_gaussNorm_le {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (a : ℕ → L) {Y : ℝ} (hY : 0 ≤ Y)
    (n : ℕ) (h : ∀ i < n, ‖a i‖ * ρ ^ i ≤ Y) :
    ConvergesAt (T.zcoeff (T.finSum a n)) ρ ∧ gaussNorm (T.zcoeff (T.finSum a n)) ρ ≤ Y := by
  have := T.gaussNorm_sum_terms_le (one_mem _) (by simp) hρ0 hρ1 a hY n fun m hm => by
    rw [mul_comm]; exact h m hm
  simpa [finSum] using this

theorem convergesAt_of_forall_weight_le {x : Γ} {ρ σ Y : ℝ} (hσ0 : 0 < σ) (hσρ : σ < ρ)
    (h : ∀ n : ℕ, ‖T.coeff x n‖ * ρ ^ n ≤ Y) : ConvergesAt (T.zcoeff x) σ := by
  have hρ0 : 0 < ρ := hσ0.trans hσρ
  have hY : 0 ≤ Y := (mul_nonneg (norm_nonneg _) (pow_pos hρ0 0).le).trans (h 0)
  have hsr0 : 0 ≤ σ / ρ := by positivity
  have hsr1 : σ / ρ < 1 := by rwa [div_lt_one hρ0]
  refine convergesAt_of_eventually hσ0 (T.zcoeff_neg_exists x) fun ε hε => ?_
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (Y + 1) by positivity) hsr1
  refine ⟨K, fun n hn => ?_⟩
  lift n to ℕ using (by omega)
  rw [zcoeff_natCast, zpow_natCast]
  have hn' : K ≤ n := by exact_mod_cast hn
  calc ‖T.coeff x n‖ * σ ^ n = (‖T.coeff x n‖ * ρ ^ n) * (σ / ρ) ^ n := by
        rw [div_pow]; field_simp
    _ ≤ Y * (σ / ρ) ^ K :=
        mul_le_mul (h n) (pow_le_pow_of_le_one hsr0 hsr1.le hn') (by positivity) hY
    _ ≤ (Y + 1) * (ε / (Y + 1)) := mul_le_mul (by linarith) hK.le (by positivity) (by linarith)
    _ = ε := by field_simp

namespace TeichFrob

variable {T} (F : T.TeichFrob)

theorem two_le_q (ha : 0 < F.a) : 2 ≤ p ^ F.a :=
  hp.out.two_le.trans (Nat.le_self_pow ha.ne' p)

theorem φ_π_pow_mul_teich (n : ℕ) (c : L) :
    F.φ (T.π ^ n * T.teich c) = T.π ^ n * (F.u ^ n * T.teich (c ^ p ^ F.a)) := by
  rw [map_mul, map_pow, F.φ_π, F.φ_teich]; ring

theorem φ_mem_span_pow {x : Γ} {n : ℕ} (hx : x ∈ Ideal.span {T.π ^ n}) :
    F.φ x ∈ Ideal.span {T.π ^ n} := by
  obtain ⟨y, rfl⟩ := T.mem_span_pow.1 hx
  rw [map_mul, map_pow, F.φ_π, mul_pow, mul_assoc]
  exact T.π_pow_mul_mem le_rfl _

theorem step_mem {w y : Γ} {n : ℕ} (hy : F.φ y - w * y ∈ Ideal.span {T.π ^ n}) {t : L}
    (ht : T.red F.u ^ n * t ^ p ^ F.a - T.red w * t + T.coeff (F.φ y - w * y) n = 0) :
    F.φ (y + T.π ^ n * T.teich t) - w * (y + T.π ^ n * T.teich t) ∈
      Ideal.span {T.π ^ (n + 1)} := by
  obtain ⟨z, hz⟩ := T.mem_span_pow.1 hy
  have he : T.coeff (F.φ y - w * y) n = T.red z := by
    rw [hz]; simpa using T.coeff_π_pow_mul_add n z 0
  have hred : T.red (z + F.u ^ n * T.teich (t ^ p ^ F.a) - w * T.teich t) = 0 := by
    rw [map_sub, map_add, map_mul, map_mul, map_pow, T.red_teich, T.red_teich, ← he]
    linear_combination ht
  obtain ⟨z', hz'⟩ := T.red_eq_zero_iff.1 hred
  have : F.φ (y + T.π ^ n * T.teich t) - w * (y + T.π ^ n * T.teich t) = T.π ^ (n + 1) * z' := by
    rw [map_add, F.φ_π_pow_mul_teich, pow_succ, mul_assoc, ← hz']
    linear_combination hz
  rw [this]; exact T.π_pow_mul_mem le_rfl _

def approx (w : Γ) (r : ℕ → L → L) : ℕ → Γ
  | 0 => 0
  | n + 1 => approx w r n +
      T.π ^ n * T.teich (r n (T.coeff (F.φ (approx w r n) - w * approx w r n) n))

def approxCoeff (w : Γ) (r : ℕ → L → L) (n : ℕ) : L :=
  r n (T.coeff (F.φ (F.approx w r n) - w * F.approx w r n) n)

theorem approx_eq_finSum (w : Γ) (r : ℕ → L → L) (n : ℕ) :
    F.approx w r n = T.finSum (F.approxCoeff w r) n := by
  induction n with
  | zero => simp [approx]
  | succ n ih => rw [T.finSum_succ, ← ih]; rfl

variable {F}

theorem approx_mem {w : Γ} {r : ℕ → L → L}
    (hr : ∀ n e, T.red F.u ^ n * r n e ^ p ^ F.a - T.red w * r n e + e = 0) (n : ℕ) :
    F.φ (F.approx w r n) - w * F.approx w r n ∈ Ideal.span {T.π ^ n} := by
  induction n with
  | zero => simp [approx]
  | succ n ih => exact F.step_mem ih (hr n _)

theorem approxCoeff_weight_le (ha : 0 < F.a) {w : Γ} {r : ℕ → L → L}
    (hr : ∀ n e, T.red F.u ^ n * r n e ^ p ^ F.a - T.red w * r n e + e = 0)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hw : ConvergesAt (T.zcoeff w) ρ) {Y : ℝ} (hY : 0 ≤ Y)
    (hW : gaussNorm (T.zcoeff w) ρ ≤ Y ^ (p ^ F.a - 1)) (n : ℕ) :
    ‖F.approxCoeff w r n‖ * ρ ^ n ≤ Y := by
  have hq := F.two_le_q ha
  set q := p ^ F.a with hqdef
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  obtain ⟨hs, hsY⟩ := T.finSum_gaussNorm_le hρ0 hρ1 (F.approxCoeff w r) hY n ih
  rw [← F.approx_eq_finSum] at hs hsY
  set s := F.approx w r n
  set σ := ρ ^ q
  have hσ0 : 0 < σ := pow_pos hρ0 _
  have hσ1 : σ < 1 := pow_lt_one₀ hρ0.le hρ1 (by omega)
  have hσρ : σ ≤ ρ := pow_le_of_le_one hρ0.le hρ1.le (by omega)
  obtain ⟨hφ, hφn⟩ := F.gaussNorm_zcoeff_map hρ0 hρ1 hs
  have hwσ : ConvergesAt (T.zcoeff w) σ := convergesAt_of_le (T.zcoeff_neg_exists w) hw hσ0 hσρ
  have hsσ : ConvergesAt (T.zcoeff s) σ := convergesAt_of_le (T.zcoeff_neg_exists s) hs hσ0 hσρ
  have hws := T.convergesAt_zcoeff_mul hσ0 hσ1 hwσ hsσ
  have hwsn : gaussNorm (T.zcoeff (w * s)) σ ≤ Y ^ q := by
    calc gaussNorm (T.zcoeff (w * s)) σ
        ≤ gaussNorm (T.zcoeff w) σ * gaussNorm (T.zcoeff s) σ :=
          T.gaussNorm_zcoeff_mul_le hσ0 hσ1.le hwσ hsσ
      _ ≤ Y ^ (q - 1) * Y :=
          mul_le_mul ((T.gaussNorm_zcoeff_mono hσ0 hσρ hw).trans hW)
            ((T.gaussNorm_zcoeff_mono hσ0 hσρ hs).trans hsY) (gaussNorm_nonneg hσ0)
            (pow_nonneg hY _)
      _ = Y ^ q := by rw [← pow_succ]; congr 1; omega
  have hneg := T.convergesAt_zcoeff_neg hσ0 hσ1 hws
  have hG : gaussNorm (T.zcoeff (F.φ s - w * s)) σ ≤ Y ^ q := by
    rw [sub_eq_add_neg]
    refine (T.gaussNorm_zcoeff_add_le hσ0 hσ1.le hφ hneg).trans (max_le ?_ ?_)
    · rw [hφn]; exact pow_le_pow_left₀ (gaussNorm_nonneg hρ0) hsY _
    · exact (T.gaussNorm_zcoeff_neg_le hσ0 hσ1.le hws).trans hwsn
  have hconv : ConvergesAt (T.zcoeff (F.φ s - w * s)) σ := by
    rw [sub_eq_add_neg]; exact T.convergesAt_zcoeff_add hσ0 hσ1 hφ hneg
  set e := T.coeff (F.φ s - w * s) n
  have hen : ‖e‖ * σ ^ n ≤ Y ^ q := by
    have := T.weight_natCast_le hconv n; rw [zpow_natCast] at this; exact this.trans hG
  have hρn0 : 0 < ρ ^ n := pow_pos hρ0 n
  have hρn1 : ρ ^ n ≤ 1 := pow_le_one₀ hρ0.le hρ1.le
  set Y' := Y / ρ ^ n
  have hYY' : Y ≤ Y' := (le_div_iff₀ hρn0).2 (mul_le_of_le_one_right hY hρn1)
  have hY' : 0 ≤ Y' := hY.trans hYY'
  have he' : ‖e‖ ≤ Y' ^ q := by
    rw [div_pow, le_div_iff₀ (pow_pos hρn0 _), ← pow_mul, mul_comm n q, pow_mul]
    exact hen
  have hb : ‖T.red w‖ ≤ Y' ^ (q - 1) := by
    have h0 := T.weight_natCast_le hw 0
    simp only [Nat.cast_zero, zpow_zero, mul_one, coeff_zero] at h0
    exact h0.trans (hW.trans (pow_le_pow_left₀ hY hYY' _))
  have hc : ‖T.red F.u ^ n‖ = 1 := by rw [norm_pow, F.norm_red_u, one_pow]
  have ht := norm_le_of_root hq hc (hr n e) hY' he' hb
  calc ‖F.approxCoeff w r n‖ * ρ ^ n ≤ Y' * ρ ^ n := mul_le_mul_of_nonneg_right ht hρn0.le
    _ = Y := div_mul_cancel₀ Y hρn0.ne'

variable (F)

theorem exists_φ_eq_mul [IsAlgClosed L] (ha : 0 < F.a) {w : Γ} (hw0 : T.red w ≠ 0) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hw : ConvergesAt (T.zcoeff w) ρ) {Y : ℝ} (hY : 0 ≤ Y)
    (hW : gaussNorm (T.zcoeff w) ρ ≤ Y ^ (p ^ F.a - 1)) :
    ∃ y : Γ, T.red y ≠ 0 ∧ F.φ y = w * y ∧ ∀ n : ℕ, ‖T.coeff y n‖ * ρ ^ n ≤ Y := by
  have hq := F.two_le_q ha
  have hu0 : ∀ n : ℕ, T.red F.u ^ n ≠ 0 := fun n =>
    pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [F.norm_red_u]; exact one_ne_zero))
  choose r hr hr0 using fun (n : ℕ) (e : L) => exists_root_of_isAlgClosed hq (hu0 n) (T.red w) e
  refine ⟨T.ofCoeff (F.approxCoeff w r), ?_, ?_, fun n => ?_⟩
  · rw [← T.coeff_zero, T.coeff_ofCoeff]
    exact hr0 0 _ (by simp [approx]) hw0
  · set y := T.ofCoeff (F.approxCoeff w r)
    have hall : ∀ n, F.φ y - w * y ∈ Ideal.span {T.π ^ n} := fun n => by
      have h1 : y - F.approx w r n ∈ Ideal.span {T.π ^ n} := by
        rw [F.approx_eq_finSum]; exact T.mk_sub_finSum_mem _ n
      have : F.φ y - w * y = (F.φ (F.approx w r n) - w * F.approx w r n) +
          (F.φ (y - F.approx w r n) - w * (y - F.approx w r n)) := by
        rw [map_sub]; ring
      rw [this]
      exact add_mem (approx_mem hr n) (sub_mem (F.φ_mem_span_pow h1) (Ideal.mul_mem_left _ _ h1))
    have h0 : F.φ y - w * y = 0 := T.eq_of_coeff_eq (funext fun n => by
      rw [T.coeff_zero_elem]; exact T.coeff_of_mem_span (hall (n + 1)) n le_rfl)
    exact sub_eq_zero.1 h0
  · rw [T.coeff_ofCoeff]
    exact approxCoeff_weight_le ha hr hρ0 hρ1 hw hY hW n

theorem exists_φ_eq_mul_of_mem_Gcon [IsAlgClosed L] (ha : 0 < F.a) {w : Γ} (hw : w ∈ T.Gcon)
    (hw0 : T.red w ≠ 0) : ∃ y ∈ T.Gcon, T.red y ≠ 0 ∧ F.φ y = w * y := by
  obtain ⟨ρ, hρ⟩ := hw
  set Y := max (gaussNorm (T.zcoeff w) ρ) 1
  have hY1 : 1 ≤ Y := le_max_right _ _
  have hW : gaussNorm (T.zcoeff w) ρ ≤ Y ^ (p ^ F.a - 1) :=
    (le_max_left _ _).trans (le_self_pow₀ hY1 (by have := F.two_le_q ha; omega))
  obtain ⟨y, hy0, hy, hyw⟩ := F.exists_φ_eq_mul ha hw0 ρ.2.1 ρ.2.2 hρ (zero_le_one.trans hY1) hW
  refine ⟨y, ⟨⟨(ρ : ℝ) / 2, by linarith [ρ.2.1], by linarith [ρ.2.2, ρ.2.1]⟩, ?_⟩, hy0, hy⟩
  exact T.convergesAt_of_forall_weight_le (by linarith [ρ.2.1]) (by linarith [ρ.2.1]) hyw

end TeichFrob

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem exists_eq_π_pow_mul {x : Γ} (hx : x ≠ 0) :
    ∃ (m : ℕ) (x' : Γ), x = T.π ^ m * x' ∧ T.red x' ≠ 0 ∧
      T.zcoeff x' = fun j => T.zcoeff x (j + m) := by
  classical
  have hex : ∃ n, T.coeff x n ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hx (T.eq_of_coeff_eq (funext fun n => by rw [h n, coeff_zero_elem]))
  set m := Nat.find hex
  have hlt : ∀ i < m, T.coeff x i = 0 := fun i hi => not_not.1 (Nat.find_min hex hi)
  have hps : T.partialSum x m = 0 := by
    simp only [partialSum, finSum]
    exact Finset.sum_eq_zero fun i hi => by rw [hlt i (Finset.mem_range.1 hi), map_zero, mul_zero]
  have heq : x = T.π ^ m * T.tail^[m] x := by
    have := T.sub_partialSum x m; rwa [hps, sub_zero] at this
  refine ⟨m, T.tail^[m] x, heq, Nat.find_spec hex, ?_⟩
  funext j
  conv_rhs => rw [heq]
  exact (T.zcoeff_π_pow_mul m _ j).symm

namespace TeichFrob

variable {T} (F : T.TeichFrob)

theorem exists_toB_eq_mul [IsAlgClosed L] (ha : 0 < F.a) {b : T.B} (hb : b ∈ T.Edag)
    (hb0 : b ≠ 0) : ∃ y ∈ T.Edag, y ≠ 0 ∧ ∃ m N : ℕ,
      algebraMap Γ T.B T.π ^ m * F.toB y = algebraMap Γ T.B T.π ^ N * b * y := by
  obtain ⟨ρ, hρ⟩ := hb
  obtain ⟨N, x, hx⟩ := IsLocalization.Away.surj T.π b
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact hb0 (T.eq_zero_of_mul_pow hx)
  have hxc : ConvergesAt (T.zcoeff x) ρ := by
    rw [T.coeffB_eq hx, convergesAt_shift_iff ρ.2.1] at hρ; exact hρ
  obtain ⟨m, x', hxx', hx'0, hz⟩ := T.exists_eq_π_pow_mul hx0
  have hx'c : x' ∈ T.Gcon := ⟨ρ, by rw [hz, convergesAt_shift_iff ρ.2.1]; exact hxc⟩
  obtain ⟨y, hyc, hy0, hy⟩ := F.exists_φ_eq_mul_of_mem_Gcon ha hx'c hx'0
  obtain ⟨σ, hσ⟩ := hyc
  refine ⟨algebraMap Γ T.B y, ⟨σ, ?_⟩, ?_, m, N, ?_⟩
  · rw [T.coeffB_algebraMap]; exact hσ
  · intro h
    have : y = 0 := T.algebraMap_injective (by rw [h, map_zero])
    exact hy0 (by rw [this, map_zero])
  · rw [F.toB_algebraMap, hy, mul_comm (algebraMap Γ T.B T.π ^ N) b, hx, ← map_pow, ← map_mul,
      ← map_mul, hxx']
    congr 1; ring

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
