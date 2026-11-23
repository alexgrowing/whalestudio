import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaDMSplit
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology

theorem tendsto_mul_pow_pow_sub_one {A θ : ℝ} (hA : 0 ≤ A) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {Q : ℕ}
    (hQ : 2 ≤ Q) : Tendsto (fun k : ℕ => A ^ k * θ ^ (Q ^ k - 1)) atTop (𝓝 0) := by
  have hQ1 : 1 < Q := by omega
  obtain ⟨j, hj⟩ : ∃ j : ℕ, A * θ ^ Q ^ j ≤ 1 / 2 := by
    have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).const_mul A
    rw [mul_zero] at h1
    obtain ⟨j, hj⟩ := (h1.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists
    refine ⟨j, le_trans ?_ hj⟩
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hθ0 hθ1.le
      (Nat.lt_pow_self hQ1).le) hA
  set B := A * θ ^ Q ^ j
  have hB0 : 0 ≤ B := by positivity
  have hlim : Tendsto (fun k : ℕ => A ^ j * (1 / 2 : ℝ) ^ (k - j)) atTop (𝓝 0) := by
    have : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ (k - j)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_sub_atTop_nat j)
    simpa using this.const_mul (A ^ j)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun k => by positivity) ?_
  filter_upwards [eventually_ge_atTop j] with k hk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hexp : Q ^ j * d ≤ Q ^ (j + d) - 1 := by
    have h1 : d + 1 ≤ Q ^ d := Nat.lt_pow_self hQ1
    have h2 : 1 ≤ Q ^ j := Nat.one_le_pow _ _ (by omega)
    rw [pow_add]
    have : Q ^ j * (d + 1) ≤ Q ^ j * Q ^ d := Nat.mul_le_mul_left _ h1
    rw [mul_add, mul_one] at this
    omega
  calc A ^ (j + d) * θ ^ (Q ^ (j + d) - 1) ≤ A ^ (j + d) * θ ^ (Q ^ j * d) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hθ0 hθ1.le hexp) (by positivity)
    _ = A ^ j * B ^ d := by rw [pow_add, pow_mul, mul_pow]; ring
    _ ≤ A ^ j * (1 / 2) ^ d :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB0 hj d) (by positivity)
    _ = A ^ j * (1 / 2) ^ (j + d - j) := by rw [Nat.add_sub_cancel_left]

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem convergesAt_of_norm_coeffB_le {b : T.B} {θ : ℝ} (hθ : 0 ≤ θ)
    (h : ∀ n, ‖T.coeffB b n‖ ≤ θ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ConvergesAt (T.coeffB b) ρ := by
  refine convergesAt_of_eventually hρ0 (T.coeffB_neg_exists b) fun ε hε => ?_
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (θ + 1) by positivity) hρ1
  refine ⟨K, fun n hn => ?_⟩
  lift n to ℕ using (by omega)
  have hn' : K ≤ n := by exact_mod_cast hn
  rw [zpow_natCast]
  calc ‖T.coeffB b n‖ * ρ ^ n ≤ (θ + 1) * ρ ^ K :=
        mul_le_mul (by linarith [h n]) (pow_le_pow_of_le_one hρ0.le hρ1.le hn') (by positivity)
          (by linarith)
    _ ≤ (θ + 1) * (ε / (θ + 1)) := mul_le_mul_of_nonneg_left hK.le (by linarith)
    _ = ε := by field_simp

theorem gaussNorm_pow_le {b : T.B} {θ : ℝ} (hθ0 : 0 ≤ θ)
    (h : ∀ n, ‖T.coeffB b n‖ ≤ θ) {Q : ℕ} (hQ : 1 ≤ Q) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    gaussNorm (T.coeffB b) σ ^ Q ≤ θ ^ (Q - 1) * gaussNorm (T.coeffB b) (σ ^ Q) := by
  have hρ0 : 0 < σ ^ Q := pow_pos hσ0 Q
  have hρ1 : σ ^ Q < 1 := pow_lt_one₀ hσ0.le hσ1 (by omega)
  have hc := T.convergesAt_of_norm_coeffB_le hθ0 h hρ0 hρ1
  set X := θ ^ (Q - 1) * gaussNorm (T.coeffB b) (σ ^ Q)
  have hX : 0 ≤ X := mul_nonneg (pow_nonneg hθ0 _) (gaussNorm_nonneg hρ0)
  have hQ0 : Q ≠ 0 := by omega
  have hterm : ∀ n : ℤ, ‖T.coeffB b n‖ * σ ^ n ≤ X ^ ((Q : ℝ)⁻¹) := by
    intro n
    have ha : 0 ≤ ‖T.coeffB b n‖ * σ ^ n := mul_nonneg (norm_nonneg _) (zpow_pos hσ0 n).le
    have hpow : (‖T.coeffB b n‖ * σ ^ n) ^ Q ≤ X := by
      have e : (‖T.coeffB b n‖ * σ ^ n) ^ Q =
          ‖T.coeffB b n‖ ^ (Q - 1) * (‖T.coeffB b n‖ * (σ ^ Q) ^ n) := by
        rw [mul_pow, ← zpow_natCast (σ ^ n), ← zpow_mul, ← zpow_natCast σ Q, ← zpow_mul,
          mul_comm n]
        rw [show ‖T.coeffB b n‖ ^ Q = ‖T.coeffB b n‖ ^ (Q - 1) * ‖T.coeffB b n‖ by
          rw [← pow_succ]; congr 1; omega]
        ring
      rw [e]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (h n) _) (hc.le_gaussNorm n)
        (mul_nonneg (norm_nonneg _) (zpow_pos hρ0 n).le) (pow_nonneg hθ0 _)
    calc ‖T.coeffB b n‖ * σ ^ n = ((‖T.coeffB b n‖ * σ ^ n) ^ Q) ^ ((Q : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast ha hQ0).symm
      _ ≤ X ^ ((Q : ℝ)⁻¹) := Real.rpow_le_rpow (pow_nonneg ha _) hpow (by positivity)
  calc gaussNorm (T.coeffB b) σ ^ Q ≤ (X ^ ((Q : ℝ)⁻¹)) ^ Q :=
        pow_le_pow_left₀ (gaussNorm_nonneg hσ0) (gaussNorm_le hterm) _
    _ = X := Real.rpow_inv_natCast_pow hX hQ0

theorem coeffB_invSelf_pow (c : ℕ) :
    T.coeffB (IsLocalization.Away.invSelf T.π ^ c) = fun k => T.zcoeff 1 (k + c) := by
  refine T.coeffB_eq ?_
  rw [T.invSelf_pow_mul_pow, map_one]

theorem gaussNorm_invSelf_pow (c : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) :
    ConvergesAt (T.coeffB (IsLocalization.Away.invSelf T.π ^ c)) ρ ∧
      gaussNorm (T.coeffB (IsLocalization.Away.invSelf T.π ^ c)) ρ = ρ ^ (-(c : ℤ)) := by
  rw [T.coeffB_invSelf_pow, convergesAt_shift_iff hρ0, gaussNorm_shift hρ0, zcoeff_one,
    gaussNorm_pi_single _ _ hρ0]
  exact ⟨convergesAt_pi_single _ _ _, by simp⟩

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

theorem exists_pow_eq_radius {Q : ℕ} (hQ : 1 ≤ Q) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ σ ^ Q = ρ :=
  ⟨ρ ^ ((Q : ℝ)⁻¹), Real.rpow_pos_of_pos hρ0 _,
    Real.rpow_lt_one hρ0.le hρ1 (by positivity), Real.rpow_inv_natCast_pow hρ0.le (by omega)⟩

namespace TeichFrob

variable (F : T.TeichFrob)

theorem one_le_q : 1 ≤ p ^ F.a := F.q_pos

theorem convergesAt_toB_of_forall {z : T.B}
    (hz : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.coeffB z) ρ) :
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.coeffB (F.toB z)) ρ := by
  intro ρ hρ0 hρ1
  obtain ⟨σ, hσ0, hσ1, rfl⟩ := exists_pow_eq_radius F.one_le_q hρ0 hρ1
  exact (F.convergesAt_coeffB_toB_iff hσ0 hσ1 z).2 (hz σ hσ0 hσ1)

theorem convergesAt_toB_iterate_of_forall {z : T.B}
    (hz : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.coeffB z) ρ) (k : ℕ) :
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.coeffB ((⇑F.toB)^[k] z)) ρ := by
  induction k with
  | zero => simpa using hz
  | succ k ih =>
    rw [Function.iterate_succ_apply']; exact F.convergesAt_toB_of_forall ih

theorem gaussNorm_toB_iterate {z : T.B} {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hz : ConvergesAt (T.coeffB z) σ) (k : ℕ) :
    ConvergesAt (T.coeffB ((⇑F.toB)^[k] z)) (σ ^ (p ^ F.a) ^ k) ∧
      gaussNorm (T.coeffB ((⇑F.toB)^[k] z)) (σ ^ (p ^ F.a) ^ k) =
        gaussNorm (T.coeffB z) σ ^ (p ^ F.a) ^ k := by
  induction k with
  | zero => simpa using hz
  | succ k ih =>
    have hk0 : 0 < σ ^ (p ^ F.a) ^ k := pow_pos hσ0 _
    have hk1 : σ ^ (p ^ F.a) ^ k < 1 := pow_lt_one₀ hσ0.le hσ1 (pow_pos F.q_pos k).ne'
    rw [Function.iterate_succ_apply', pow_succ, pow_mul]
    refine ⟨(F.convergesAt_coeffB_toB_iff hk0 hk1 _).2 ih.1, ?_⟩
    rw [F.gaussNorm_coeffB_toB hk0 hk1 ih.1, ih.2, ← pow_mul]

theorem gaussNorm_toB_iterate_le {w : T.B} {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hw : ∀ n, ‖T.coeffB w n‖ ≤ θ) (k : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ConvergesAt (T.coeffB ((⇑F.toB)^[k] w)) ρ ∧
      gaussNorm (T.coeffB ((⇑F.toB)^[k] w)) ρ ≤
        θ ^ ((p ^ F.a) ^ k - 1) * gaussNorm (T.coeffB w) ρ := by
  have hQ : 1 ≤ (p ^ F.a) ^ k := Nat.one_le_pow _ _ F.q_pos
  obtain ⟨σ, hσ0, hσ1, rfl⟩ := exists_pow_eq_radius hQ hρ0 hρ1
  obtain ⟨h1, h2⟩ := F.gaussNorm_toB_iterate hσ0 hσ1
    (T.convergesAt_of_norm_coeffB_le hθ0 hw hσ0 hσ1) k
  exact ⟨h1, h2 ▸ T.gaussNorm_pow_le hθ0 hw hQ hσ0 hσ1⟩

def fwd (c : ℕ) (z : T.B) : T.B := IsLocalization.Away.invSelf T.π ^ c * F.toB z

theorem toB_eq_fwd (c : ℕ) (z : T.B) : F.toB z = algebraMap Γ T.B T.π ^ c * F.fwd c z := by
  rw [fwd, ← mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, one_mul]

theorem gaussNorm_fwd_iterate (c : ℕ) {z : T.B}
    (hz : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.coeffB z) ρ) (k : ℕ) :
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.coeffB ((F.fwd c)^[k] z)) ρ ∧
      gaussNorm (T.coeffB ((F.fwd c)^[k] z)) ρ =
        ρ ^ (-((c * k : ℕ) : ℤ)) * gaussNorm (T.coeffB ((⇑F.toB)^[k] z)) ρ := by
  induction k with
  | zero => intro ρ hρ0 hρ1; simpa using hz ρ hρ0 hρ1
  | succ k ih =>
    intro ρ hρ0 hρ1
    obtain ⟨σ, hσ0, hσ1, rfl⟩ := exists_pow_eq_radius F.one_le_q hρ0 hρ1
    obtain ⟨ih1, ih2⟩ := ih σ hσ0 hσ1
    have hq0 : 0 < σ ^ p ^ F.a := pow_pos hσ0 _
    have hq1 : σ ^ p ^ F.a < 1 := pow_lt_one₀ hσ0.le hσ1 F.q_pos.ne'
    have htw := (F.convergesAt_coeffB_toB_iff hσ0 hσ1 _).2 ih1
    obtain ⟨hi1, hi2⟩ := T.gaussNorm_invSelf_pow c hq0
    obtain ⟨hm1, hm2⟩ := T.convergesAt_coeffB_mul hq0 hq1 hi1 htw
    have hzk := F.convergesAt_toB_iterate_of_forall hz k σ hσ0 hσ1
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine ⟨hm1, ?_⟩
    change gaussNorm (T.coeffB (IsLocalization.Away.invSelf T.π ^ c * F.toB _)) _ = _
    rw [hm2, hi2, F.gaussNorm_coeffB_toB hσ0 hσ1 ih1, ih2, mul_pow,
      ← F.gaussNorm_coeffB_toB hσ0 hσ1 hzk, ← mul_assoc]
    congr 1
    rw [← zpow_natCast σ (p ^ F.a), ← zpow_mul, ← zpow_natCast (σ ^ (-((c * k : ℕ) : ℤ))),
      ← zpow_mul, ← zpow_mul, ← zpow_add₀ hσ0.ne']
    congr 1
    push_cast; ring

end TeichFrob

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem coeffB_zero_B : T.coeffB 0 = 0 := by
  rw [← map_zero (algebraMap Γ T.B), coeffB_algebraMap, (T.zcoeff_eq_zero_iff 0).2 rfl]

theorem gaussNorm_finsetSum_le {ι : Type*} (s : Finset ι) (f : ι → T.B) {ρ M : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hM : 0 ≤ M)
    (h : ∀ i ∈ s, ConvergesAt (T.coeffB (f i)) ρ ∧ gaussNorm (T.coeffB (f i)) ρ ≤ M) :
    ConvergesAt (T.coeffB (∑ i ∈ s, f i)) ρ ∧ gaussNorm (T.coeffB (∑ i ∈ s, f i)) ρ ≤ M := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, T.coeffB_zero_B]
    exact ⟨convergesAt_zero, by simp [gaussNorm, hM]⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    obtain ⟨h1, h2⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨h3, h4⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    obtain ⟨h5, h6⟩ := T.convergesAt_coeffB_add hρ0 hρ1 h1 h3
    exact ⟨h5, h6.trans (max_le h2 h4)⟩

namespace TeichFrob

variable {T} (F : T.TeichFrob)

theorem gaussNorm_fwd_iterate_le (c : ℕ) {w : T.B} {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hw : ∀ n, ‖T.coeffB w n‖ ≤ θ) (k : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ConvergesAt (T.coeffB ((F.fwd c)^[k] w)) ρ ∧
      gaussNorm (T.coeffB ((F.fwd c)^[k] w)) ρ ≤
        ρ ^ (-((c * k : ℕ) : ℤ)) * θ ^ ((p ^ F.a) ^ k - 1) * gaussNorm (T.coeffB w) ρ := by
  obtain ⟨h1, h2⟩ := F.gaussNorm_fwd_iterate c
    (fun σ hσ0 hσ1 => T.convergesAt_of_norm_coeffB_le hθ0 hw hσ0 hσ1) k ρ hρ0 hρ1
  refine ⟨h1, ?_⟩
  rw [h2, mul_assoc]
  exact mul_le_mul_of_nonneg_left (F.gaussNorm_toB_iterate_le hθ0 hw k hρ0 hρ1).2
    (zpow_pos hρ0 _).le

def fwdSum (c : ℕ) (w : T.B) (K : ℕ) : T.B := -∑ k ∈ Finset.range K, (F.fwd c)^[k] w

theorem toB_fwdSum_sub (c : ℕ) (w : T.B) (K : ℕ) :
    F.toB (F.fwdSum c w K) - algebraMap Γ T.B T.π ^ c * F.fwdSum c w K =
      algebraMap Γ T.B T.π ^ c * w - algebraMap Γ T.B T.π ^ c * (F.fwd c)^[K] w := by
  induction K with
  | zero => simp [fwdSum]
  | succ K ih =>
    have e : F.fwdSum c w (K + 1) = F.fwdSum c w K - (F.fwd c)^[K] w := by
      simp only [fwdSum, Finset.sum_range_succ]; ring
    rw [e, map_sub, F.toB_eq_fwd c ((F.fwd c)^[K] w), ← Function.iterate_succ_apply' (F.fwd c)]
    linear_combination ih

theorem gaussNorm_fwdSum_sub_le (c : ℕ) {w : T.B} {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hw : ∀ n, ‖T.coeffB w n‖ ≤ θ) {K K' : ℕ} (hKK' : K ≤ K') {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ k, K ≤ k → ρ ^ (-((c * k : ℕ) : ℤ)) * θ ^ ((p ^ F.a) ^ k - 1) *
      gaussNorm (T.coeffB w) ρ ≤ M) :
    ConvergesAt (T.coeffB (F.fwdSum c w K' - F.fwdSum c w K)) ρ ∧
      gaussNorm (T.coeffB (F.fwdSum c w K' - F.fwdSum c w K)) ρ ≤ M := by
  have e : F.fwdSum c w K' - F.fwdSum c w K = -∑ k ∈ Finset.Ico K K', (F.fwd c)^[k] w := by
    simp only [fwdSum, Finset.sum_Ico_eq_sub _ hKK']; ring
  rw [e]
  obtain ⟨h1, h2⟩ := T.gaussNorm_finsetSum_le (Finset.Ico K K') (fun k => (F.fwd c)^[k] w) hρ0 hρ1 hM
    fun k hk => by
      obtain ⟨h3, h4⟩ := F.gaussNorm_fwd_iterate_le c hθ0 hw k hρ0 hρ1
      exact ⟨h3, h4.trans (h k (Finset.mem_Ico.1 hk).1)⟩
  obtain ⟨h5, h6⟩ := T.convergesAt_coeffB_neg hρ0 hρ1 h1
  exact ⟨h5, h6 ▸ h2⟩

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
