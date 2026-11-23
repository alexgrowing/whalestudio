import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaDMRankOne
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

variable (F : T.TeichFrob)

theorem linStep_mem {α γ y x : Γ} {n : ℕ}
    (hx : α * F.φ x - γ * x - y ∈ Ideal.span {T.π ^ n}) {t : L}
    (ht : T.red α * T.red F.u ^ n * t ^ p ^ F.a - T.red γ * t +
      T.coeff (α * F.φ x - γ * x - y) n = 0) :
    α * F.φ (x + T.π ^ n * T.teich t) - γ * (x + T.π ^ n * T.teich t) - y ∈
      Ideal.span {T.π ^ (n + 1)} := by
  obtain ⟨z, hz⟩ := T.mem_span_pow.1 hx
  have he : T.coeff (α * F.φ x - γ * x - y) n = T.red z := by
    rw [hz]; simpa using T.coeff_π_pow_mul_add n z 0
  have hred : T.red (z + α * (F.u ^ n * T.teich (t ^ p ^ F.a)) - γ * T.teich t) = 0 := by
    rw [map_sub, map_add, map_mul, map_mul, map_mul, map_pow, T.red_teich, T.red_teich, ← he]
    linear_combination ht
  obtain ⟨z', hz'⟩ := T.red_eq_zero_iff.1 hred
  have : α * F.φ (x + T.π ^ n * T.teich t) - γ * (x + T.π ^ n * T.teich t) - y =
      T.π ^ (n + 1) * z' := by
    rw [map_add, F.φ_π_pow_mul_teich, pow_succ, mul_assoc, ← hz']
    linear_combination hz
  rw [this]; exact T.π_pow_mul_mem le_rfl _

def linApprox (α γ y : Γ) (r : ℕ → L → L) : ℕ → Γ
  | 0 => 0
  | n + 1 => linApprox α γ y r n + T.π ^ n * T.teich (r n
      (T.coeff (α * F.φ (linApprox α γ y r n) - γ * linApprox α γ y r n - y) n))

def linCoeff (α γ y : Γ) (r : ℕ → L → L) (n : ℕ) : L :=
  r n (T.coeff (α * F.φ (F.linApprox α γ y r n) - γ * F.linApprox α γ y r n - y) n)

theorem linApprox_eq_finSum (α γ y : Γ) (r : ℕ → L → L) (n : ℕ) :
    F.linApprox α γ y r n = T.finSum (F.linCoeff α γ y r) n := by
  induction n with
  | zero => simp [linApprox]
  | succ n ih => rw [T.finSum_succ, ← ih]; rfl

variable {F}

theorem linApprox_mem {α γ y : Γ} {r : ℕ → L → L}
    (hr : ∀ n e, T.red α * T.red F.u ^ n * r n e ^ p ^ F.a - T.red γ * r n e + e = 0) (n : ℕ) :
    α * F.φ (F.linApprox α γ y r n) - γ * F.linApprox α γ y r n - y ∈ Ideal.span {T.π ^ n} := by
  induction n with
  | zero => simp [linApprox]
  | succ n ih => exact F.linStep_mem ih (hr n _)

end TeichFrob

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

variable {F : T.TeichFrob}

theorem linCoeff_weight_le (ha : 0 < F.a) {α γ y : Γ} (hα : α ∈ T.int) {r : ℕ → L → L}
    (hr : ∀ n e, T.red α * T.red F.u ^ n * r n e ^ p ^ F.a - T.red γ * r n e + e = 0)
    (hα1 : ‖T.red α‖ = 1) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hγ : ConvergesAt (T.zcoeff γ) ρ) (hy : ConvergesAt (T.zcoeff y) ρ) {Y : ℝ} (hY : 0 ≤ Y)
    (hγY : gaussNorm (T.zcoeff γ) ρ ≤ Y ^ (p ^ F.a - 1))
    (hyY : gaussNorm (T.zcoeff y) ρ ≤ Y ^ p ^ F.a) (n : ℕ) :
    ‖F.linCoeff α γ y r n‖ * ρ ^ n ≤ Y := by
  have hq := F.two_le_q ha
  set q := p ^ F.a with hqdef
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  obtain ⟨hs, hsY⟩ := T.finSum_gaussNorm_le hρ0 hρ1 (F.linCoeff α γ y r) hY n ih
  rw [← F.linApprox_eq_finSum] at hs hsY
  set s := F.linApprox α γ y r n
  set σ := ρ ^ q
  have hσ0 : 0 < σ := pow_pos hρ0 _
  have hσ1 : σ < 1 := pow_lt_one₀ hρ0.le hρ1 (by omega)
  have hσρ : σ ≤ ρ := pow_le_of_le_one hρ0.le hρ1.le (by omega)
  obtain ⟨hφ, hφn⟩ := F.gaussNorm_zcoeff_map hρ0 hρ1 hs
  have hασ := T.convergesAt_of_mem_int hα hσ0 hσ1
  have hαφ := T.convergesAt_zcoeff_mul hσ0 hσ1 hασ hφ
  have hαφn : gaussNorm (T.zcoeff (α * F.φ s)) σ ≤ Y ^ q := by
    calc gaussNorm (T.zcoeff (α * F.φ s)) σ
        ≤ gaussNorm (T.zcoeff α) σ * gaussNorm (T.zcoeff (F.φ s)) σ :=
          T.gaussNorm_zcoeff_mul_le hσ0 hσ1.le hασ hφ
      _ ≤ 1 * Y ^ q := by
          refine mul_le_mul (T.gaussNorm_le_one_of_mem_int hα hσ0 hσ1.le) ?_
            (gaussNorm_nonneg hσ0) zero_le_one
          rw [hφn]; exact pow_le_pow_left₀ (gaussNorm_nonneg hρ0) hsY _
      _ = Y ^ q := one_mul _
  have hγσ : ConvergesAt (T.zcoeff γ) σ := convergesAt_of_le (T.zcoeff_neg_exists γ) hγ hσ0 hσρ
  have hsσ : ConvergesAt (T.zcoeff s) σ := convergesAt_of_le (T.zcoeff_neg_exists s) hs hσ0 hσρ
  have hyσ : ConvergesAt (T.zcoeff y) σ := convergesAt_of_le (T.zcoeff_neg_exists y) hy hσ0 hσρ
  have hγs := T.convergesAt_zcoeff_mul hσ0 hσ1 hγσ hsσ
  have hγsn : gaussNorm (T.zcoeff (γ * s)) σ ≤ Y ^ q := by
    calc gaussNorm (T.zcoeff (γ * s)) σ
        ≤ gaussNorm (T.zcoeff γ) σ * gaussNorm (T.zcoeff s) σ :=
          T.gaussNorm_zcoeff_mul_le hσ0 hσ1.le hγσ hsσ
      _ ≤ Y ^ (q - 1) * Y :=
          mul_le_mul ((T.gaussNorm_zcoeff_mono hσ0 hσρ hγ).trans hγY)
            ((T.gaussNorm_zcoeff_mono hσ0 hσρ hs).trans hsY) (gaussNorm_nonneg hσ0)
            (pow_nonneg hY _)
      _ = Y ^ q := by rw [← pow_succ]; congr 1; omega
  have hyn : gaussNorm (T.zcoeff y) σ ≤ Y ^ q := (T.gaussNorm_zcoeff_mono hσ0 hσρ hy).trans hyY
  have hn1 := T.convergesAt_zcoeff_neg hσ0 hσ1 hγs
  have hn2 := T.convergesAt_zcoeff_neg hσ0 hσ1 hyσ
  have hc1 := T.convergesAt_zcoeff_add hσ0 hσ1 hαφ hn1
  have hE : α * F.φ s - γ * s - y = (α * F.φ s + -(γ * s)) + -y := by ring
  have hG : gaussNorm (T.zcoeff (α * F.φ s - γ * s - y)) σ ≤ Y ^ q := by
    rw [hE]
    refine (T.gaussNorm_zcoeff_add_le hσ0 hσ1.le hc1 hn2).trans (max_le ?_ ?_)
    · refine (T.gaussNorm_zcoeff_add_le hσ0 hσ1.le hαφ hn1).trans (max_le hαφn ?_)
      exact (T.gaussNorm_zcoeff_neg_le hσ0 hσ1.le hγs).trans hγsn
    · exact (T.gaussNorm_zcoeff_neg_le hσ0 hσ1.le hyσ).trans hyn
  have hconv : ConvergesAt (T.zcoeff (α * F.φ s - γ * s - y)) σ := by
    rw [hE]; exact T.convergesAt_zcoeff_add hσ0 hσ1 hc1 hn2
  set e := T.coeff (α * F.φ s - γ * s - y) n
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
  have hb : ‖T.red γ‖ ≤ Y' ^ (q - 1) := by
    have h0 := T.weight_natCast_le hγ 0
    simp only [Nat.cast_zero, zpow_zero, mul_one, coeff_zero] at h0
    exact h0.trans (hγY.trans (pow_le_pow_left₀ hY hYY' _))
  have hc : ‖T.red α * T.red F.u ^ n‖ = 1 := by rw [norm_mul, norm_pow, F.norm_red_u, one_pow, hα1, one_mul]
  have ht := norm_le_of_root hq hc (hr n e) hY' he' hb
  calc ‖F.linCoeff α γ y r n‖ * ρ ^ n ≤ Y' * ρ ^ n := mul_le_mul_of_nonneg_right ht hρn0.le
    _ = Y := div_mul_cancel₀ Y hρn0.ne'

variable (F)

theorem exists_linear_sol [IsAlgClosed L] (ha : 0 < F.a) {α : Γ} (hα : α ∈ T.int)
    (hα1 : ‖T.red α‖ = 1) (γ y : Γ) :
    ∃ x : Γ, α * F.φ x - γ * x = y ∧ ∀ ρ Y : ℝ, 0 < ρ → ρ < 1 →
      ConvergesAt (T.zcoeff γ) ρ → ConvergesAt (T.zcoeff y) ρ → 0 ≤ Y →
      gaussNorm (T.zcoeff γ) ρ ≤ Y ^ (p ^ F.a - 1) → gaussNorm (T.zcoeff y) ρ ≤ Y ^ p ^ F.a →
      ∀ n : ℕ, ‖T.coeff x n‖ * ρ ^ n ≤ Y := by
  have hq := F.two_le_q ha
  have hc0 : ∀ n : ℕ, T.red α * T.red F.u ^ n ≠ 0 := fun n => by
    refine mul_ne_zero (norm_ne_zero_iff.1 (by rw [hα1]; exact one_ne_zero))
      (pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [F.norm_red_u]; exact one_ne_zero)))
  choose r hr _ using fun (n : ℕ) (e : L) => exists_root_of_isAlgClosed hq (hc0 n) (T.red γ) e
  refine ⟨T.ofCoeff (F.linCoeff α γ y r), ?_, fun ρ Y hρ0 hρ1 hγ hy hY hγY hyY n => ?_⟩
  · set x := T.ofCoeff (F.linCoeff α γ y r)
    have hall : ∀ n, α * F.φ x - γ * x - y ∈ Ideal.span {T.π ^ n} := fun n => by
      have h1 : x - F.linApprox α γ y r n ∈ Ideal.span {T.π ^ n} := by
        rw [F.linApprox_eq_finSum]; exact T.mk_sub_finSum_mem _ n
      have : α * F.φ x - γ * x - y = (α * F.φ (F.linApprox α γ y r n) - γ * F.linApprox α γ y r n - y) +
          (α * F.φ (x - F.linApprox α γ y r n) - γ * (x - F.linApprox α γ y r n)) := by
        rw [map_sub]; ring
      rw [this]
      exact add_mem (linApprox_mem hr n)
        (sub_mem (Ideal.mul_mem_left _ _ (F.φ_mem_span_pow h1)) (Ideal.mul_mem_left _ _ h1))
    have h0 : α * F.φ x - γ * x - y = 0 := T.eq_of_coeff_eq (funext fun n => by
      rw [T.coeff_zero_elem]; exact T.coeff_of_mem_span (hall (n + 1)) n le_rfl)
    exact sub_eq_zero.1 h0
  · rw [T.coeff_ofCoeff]
    exact linCoeff_weight_le ha hα hr hα1 hρ0 hρ1 hγ hy hY hγY hyY n

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
