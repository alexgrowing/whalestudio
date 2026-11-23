import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaDMForward
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology

section Seq

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem convergesAt_of_weight_le {a : ℤ → K} {ρ σ Y : ℝ} (hσ0 : 0 < σ) (hσρ : σ < ρ)
    (hneg : ∃ N, ∀ n < N, a n = 0) (h : ∀ n, ‖a n‖ * ρ ^ n ≤ Y) : ConvergesAt a σ := by
  have hρ0 : 0 < ρ := hσ0.trans hσρ
  have hY : 0 ≤ Y := (mul_nonneg (norm_nonneg _) (zpow_pos hρ0 0).le).trans (h 0)
  have hsr0 : 0 ≤ σ / ρ := by positivity
  have hsr1 : σ / ρ < 1 := by rwa [div_lt_one hρ0]
  refine convergesAt_of_eventually hσ0 hneg fun ε hε => ?_
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (Y + 1) by positivity) hsr1
  refine ⟨M, fun n hn => ?_⟩
  lift n to ℕ using (by omega)
  have hn' : M ≤ n := by exact_mod_cast hn
  rw [zpow_natCast]
  calc ‖a n‖ * σ ^ n = (‖a n‖ * ρ ^ (n : ℤ)) * (σ / ρ) ^ n := by
        rw [div_pow, zpow_natCast]; field_simp
    _ ≤ Y * (σ / ρ) ^ M :=
        mul_le_mul (h n) (pow_le_pow_of_le_one hsr0 hsr1.le hn') (by positivity) hY
    _ ≤ (Y + 1) * (ε / (Y + 1)) := mul_le_mul (by linarith) hM.le (by positivity) (by linarith)
    _ = ε := by field_simp

end Seq

def fwdConst (q c : ℕ) (ρ : ℝ) : ℝ := ⨆ k : ℕ, ρ ^ (-((c * k : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ (q ^ k - 1)

theorem tendsto_fwdConst_terms {q : ℕ} (hq : 2 ≤ q) (c : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) :
    Tendsto (fun k : ℕ => ρ ^ (-((c * k : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ (q ^ k - 1)) atTop (𝓝 0) := by
  have := tendsto_mul_pow_pow_sub_one (A := (ρ ^ c)⁻¹) (by positivity) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num) hq
  refine this.congr fun k => ?_
  rw [inv_pow, ← pow_mul, ← zpow_natCast, ← zpow_neg]

theorem le_fwdConst {q : ℕ} (hq : 2 ≤ q) (c : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) (k : ℕ) :
    ρ ^ (-((c * k : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ (q ^ k - 1) ≤ fwdConst q c ρ :=
  le_ciSup (tendsto_fwdConst_terms hq c hρ0).bddAbove_range k

theorem fwdConst_nonneg {q : ℕ} (hq : 2 ≤ q) (c : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) :
    0 ≤ fwdConst q c ρ :=
  (by positivity : (0 : ℝ) ≤ ρ ^ (-((c * 0 : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ (q ^ 0 - 1)).trans
    (le_fwdConst hq c hρ0 0)

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem coeffB_invSelf_pow_mul (c : ℕ) (b : T.B) (n : ℤ) :
    T.coeffB (IsLocalization.Away.invSelf T.π ^ c * b) n = T.coeffB b (n + c) := by
  have h : (IsLocalization.Away.invSelf T.π ^ c * b) * algebraMap Γ T.B T.π ^ (T.den b + c) =
      algebraMap Γ T.B (T.num b) := by
    rw [pow_add, ← T.num_spec b]
    calc IsLocalization.Away.invSelf T.π ^ c * b *
          (algebraMap Γ T.B T.π ^ T.den b * algebraMap Γ T.B T.π ^ c)
        = b * algebraMap Γ T.B T.π ^ T.den b *
          (IsLocalization.Away.invSelf T.π ^ c * algebraMap Γ T.B T.π ^ c) := by ring
      _ = _ := by rw [T.invSelf_pow_mul_pow, mul_one]
  rw [T.coeffB_eq h, T.coeffB_eq (T.num_spec b)]
  simp only
  congr 1; push_cast; ring

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

theorem gaussNorm_π_pow (c : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) :
    ConvergesAt (T.coeffB (algebraMap Γ T.B T.π ^ c)) ρ ∧
      gaussNorm (T.coeffB (algebraMap Γ T.B T.π ^ c)) ρ = ρ ^ c := by
  rw [← map_pow, T.coeffB_algebraMap, zcoeff_π_pow, gaussNorm_pi_single _ _ hρ0]
  exact ⟨convergesAt_pi_single _ _ _, by simp⟩

namespace TeichFrob

variable (F : T.TeichFrob)

theorem exists_approx_sol [IsAlgClosed L] (ha : 0 < F.a) (c : ℕ) {d : T.B}
    (hd : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.coeffB d) ρ) (K : ℕ) :
    ∃ t R : T.B, F.toB t - algebraMap Γ T.B T.π ^ c * t = d - R ∧
      (∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.coeffB t) ρ ∧
        gaussNorm (T.coeffB t) ρ ≤
          max 2 (fwdConst (p ^ F.a) c ρ * ρ ^ (-(c : ℤ))) * gaussNorm (T.coeffB d) ρ) ∧
      (∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.coeffB R) ρ ∧
        gaussNorm (T.coeffB R) ρ ≤
          ρ ^ (-((c * K : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ ((p ^ F.a) ^ K - 1) *
            gaussNorm (T.coeffB d) ρ) := by
  have hq := F.two_le_q ha
  have hθ0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hsd : T.smallPart (1 / 2) d + T.bigPart (1 / 2) d = d := T.smallPart_add_bigPart _ d
  obtain ⟨w, hwdef⟩ : ∃ w, IsLocalization.Away.invSelf T.π ^ c * T.smallPart (1 / 2) d = w :=
    ⟨_, rfl⟩
  have hw : ∀ n, ‖T.coeffB w n‖ ≤ 1 / 2 := fun n => by
    rw [← hwdef, T.coeffB_invSelf_pow_mul]; exact (T.norm_coeffB_smallPart_lt hθ0 d _).le
  have hπw : algebraMap Γ T.B T.π ^ c * w = T.smallPart (1 / 2) d := by
    rw [← hwdef, ← mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, one_mul]
  obtain ⟨z, hz, hzb⟩ := F.exists_sol_big ha c hθ0 (by norm_num)
    (T.coeffB_bigPart_eq_zero_or (1 / 2) d)
  refine ⟨z + F.fwdSum c w K, algebraMap Γ T.B T.π ^ c * (F.fwd c)^[K] w, ?_, ?_, ?_⟩
  · have h1 := F.toB_fwdSum_sub c w K
    rw [hπw] at h1
    rw [map_add, ← hsd]
    linear_combination hz + h1
  · intro ρ hρ0 hρ1
    have hdρ := hd ρ hρ0 hρ1
    obtain ⟨hbρ, hbρn⟩ := convergesAt_of_norm_le hρ0 (T.norm_coeffB_bigPart_le (1 / 2) d) hdρ
    obtain ⟨hsρ, hsρn⟩ := convergesAt_of_norm_le hρ0 (T.norm_coeffB_smallPart_le hθ0 d) hdρ

    obtain ⟨ρ', hρ'0, hρ'1, hρρ'⟩ : ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' < 1 ∧ ρ < ρ' :=
      ⟨(ρ + 1) / 2, by positivity, by linarith, by linarith⟩
    obtain ⟨hbρ', -⟩ := convergesAt_of_norm_le hρ'0 (T.norm_coeffB_bigPart_le (1 / 2) d)
      (hd ρ' hρ'0 hρ'1)
    have hzc : ConvergesAt (T.coeffB z) ρ :=
      convergesAt_of_weight_le hρ0 hρρ' (T.coeffB_neg_exists z) (hzb ρ' hρ'0 hρ'1 hbρ')
    have hzn : gaussNorm (T.coeffB z) ρ ≤ 2 * gaussNorm (T.coeffB d) ρ := by
      refine gaussNorm_le fun n => (hzb ρ hρ0 hρ1 hbρ n).trans ?_
      rw [show ((1 : ℝ) / 2)⁻¹ = 2 by norm_num]
      exact mul_le_mul_of_nonneg_left hbρn (by norm_num)

    obtain ⟨hi1, hi2⟩ := T.gaussNorm_invSelf_pow c hρ0
    obtain ⟨hwc, hwn⟩ := T.convergesAt_coeffB_mul hρ0 hρ1 hi1 hsρ
    rw [hwdef] at hwc hwn
    have hwd : gaussNorm (T.coeffB w) ρ ≤ ρ ^ (-(c : ℤ)) * gaussNorm (T.coeffB d) ρ := by
      rw [hwn, hi2]; exact mul_le_mul_of_nonneg_left hsρn (zpow_pos hρ0 _).le
    have hM : 0 ≤ fwdConst (p ^ F.a) c ρ * ρ ^ (-(c : ℤ)) * gaussNorm (T.coeffB d) ρ :=
      mul_nonneg (mul_nonneg (fwdConst_nonneg hq c hρ0) (zpow_pos hρ0 _).le) (gaussNorm_nonneg hρ0)
    obtain ⟨hSc, hSn⟩ := F.gaussNorm_fwdSum_sub_le c hθ0.le hw (Nat.zero_le K) hρ0 hρ1 hM
      fun k _ => by
        rw [mul_assoc (fwdConst _ _ _)]
        exact mul_le_mul (le_fwdConst hq c hρ0 k) hwd (gaussNorm_nonneg hρ0)
          (fwdConst_nonneg hq c hρ0)
    have e0 : F.fwdSum c w 0 = 0 := by simp [fwdSum]
    rw [e0, sub_zero] at hSc hSn
    obtain ⟨htc, htn⟩ := T.convergesAt_coeffB_add hρ0 hρ1 hzc hSc
    refine ⟨htc, htn.trans ?_⟩
    rw [max_mul_of_nonneg _ _ (gaussNorm_nonneg hρ0)]
    exact max_le_max hzn (by rw [mul_assoc] at hSn ⊢; exact hSn)
  · intro ρ hρ0 hρ1
    have hdρ := hd ρ hρ0 hρ1
    obtain ⟨hsρ, hsρn⟩ := convergesAt_of_norm_le hρ0 (T.norm_coeffB_smallPart_le hθ0 d) hdρ
    obtain ⟨hi1, hi2⟩ := T.gaussNorm_invSelf_pow c hρ0
    obtain ⟨-, hwn⟩ := T.convergesAt_coeffB_mul hρ0 hρ1 hi1 hsρ
    rw [hwdef] at hwn
    obtain ⟨hKc, hKn⟩ := F.gaussNorm_fwd_iterate_le c hθ0.le hw K hρ0 hρ1
    obtain ⟨hp1, hp2⟩ := gaussNorm_π_pow (T := T) c hρ0
    obtain ⟨hRc, hRn⟩ := T.convergesAt_coeffB_mul hρ0 hρ1 hp1 hKc
    refine ⟨hRc, ?_⟩
    rw [hRn, hp2]
    calc ρ ^ c * gaussNorm (T.coeffB ((F.fwd c)^[K] w)) ρ
        ≤ ρ ^ c * (ρ ^ (-((c * K : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ ((p ^ F.a) ^ K - 1) *
            (ρ ^ (-(c : ℤ)) * gaussNorm (T.coeffB d) ρ)) := by
          refine mul_le_mul_of_nonneg_left (hKn.trans ?_) (pow_pos hρ0 c).le
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hwn, hi2]; exact mul_le_mul_of_nonneg_left hsρn (zpow_pos hρ0 _).le
      _ = ρ ^ (-((c * K : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ ((p ^ F.a) ^ K - 1) *
            gaussNorm (T.coeffB d) ρ := by
          rw [← zpow_natCast ρ c]
          have : ρ ^ (c : ℤ) * ρ ^ (-(c : ℤ)) = 1 := by
            rw [← zpow_add₀ hρ0.ne', add_neg_cancel, zpow_zero]
          linear_combination (ρ ^ (-((c * K : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ ((p ^ F.a) ^ K - 1) *
            gaussNorm (T.coeffB d) ρ) * this

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
