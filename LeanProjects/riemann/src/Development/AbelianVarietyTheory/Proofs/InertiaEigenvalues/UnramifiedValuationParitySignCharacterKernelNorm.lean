import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.EtaChar

theorem exists_unif (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] :
    ∃ π : F, 0 < ‖π‖ ∧ ‖π‖ < 1 ∧ ∀ x : F, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have hc : IsCompact (Metric.ball (0 : F) 1) :=
    (isCompact_closedBall (0 : F) 1).of_isClosed_subset (IsUltrametricDist.isClosed_ball _ _)
      Metric.ball_subset_closedBall
  obtain ⟨π, hπm, hmax⟩ := hc.exists_isMaxOn ⟨0, Metric.mem_ball_self one_pos⟩ continuous_norm.continuousOn
  have hπ1 : ‖π‖ < 1 := by simpa using hπm
  have hle : ∀ y : F, ‖y‖ < 1 → ‖y‖ ≤ ‖π‖ := fun y hy => hmax (by simpa using hy)
  obtain ⟨x0, hx0, hx01⟩ := NormedField.exists_norm_lt_one F
  have hπ0 : 0 < ‖π‖ := lt_of_lt_of_le hx0 (hle x0 hx01)
  refine ⟨π, hπ0, hπ1, fun x hx => ?_⟩
  set q := ‖π‖ with hq
  have hxp : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hqi : 1 < q⁻¹ := one_lt_inv₀ hπ0 |>.2 hπ1
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hxp hqi
  have hqn : 0 < q ^ (n + 1) := zpow_pos hπ0 _
  have hz : ‖x * π ^ (n + 1)‖ = ‖x‖ * q ^ (n + 1) := by rw [norm_mul, norm_zpow]
  have hup : ‖x‖ * q ^ (n + 1) ≤ 1 := by
    calc ‖x‖ * q ^ (n + 1) ≤ q⁻¹ ^ (n + 1) * q ^ (n + 1) := mul_le_mul_of_nonneg_right hn2 hqn.le
      _ = 1 := by rw [_root_.inv_zpow, inv_mul_cancel₀ hqn.ne']
  have hlo : q < ‖x‖ * q ^ (n + 1) := by
    calc q = q⁻¹ ^ n * q ^ (n + 1) := by
            rw [_root_.inv_zpow, zpow_add_one₀ hπ0.ne', ← mul_assoc, inv_mul_cancel₀ (zpow_pos hπ0 n).ne', one_mul]
      _ < ‖x‖ * q ^ (n + 1) := mul_lt_mul_of_pos_right hn1 hqn
  have heq : ‖x‖ * q ^ (n + 1) = 1 := by
    by_contra hne
    have := hle (x * π ^ (n + 1)) (by rw [hz]; exact lt_of_le_of_ne hup hne)
    rw [hz] at this
    linarith
  refine ⟨-(n + 1), ?_⟩
  rw [_root_.zpow_neg]; exact eq_inv_of_mul_eq_one_left heq

theorem eta_eq_one_iff {F : Type} [NormedField F] (x : F) : eta x = 1 ↔ ∃ y : F, ‖x‖ = ‖y‖ ^ 2 := by
  unfold eta
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    norm_num

theorem eta_eq_neg_one_iff {F : Type} [NormedField F] (x : F) : eta x = -1 ↔ ¬ ∃ y : F, ‖x‖ = ‖y‖ ^ 2 := by
  unfold eta
  split_ifs with h
  · simp only [h, not_true_eq_false, iff_false]
    norm_num
  · simp [h]

theorem sq_iff_even {F : Type} [NormedField F] {π : F} (h0 : 0 < ‖π‖) (h1 : ‖π‖ < 1)
    (hall : ∀ x : F, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k) {x : F} {k : ℤ} (hk : ‖x‖ = ‖π‖ ^ k) :
    (∃ y : F, ‖x‖ = ‖y‖ ^ 2) ↔ Even k := by
  constructor
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      have : ‖x‖ = 0 := by simpa using hy
      rw [hk] at this
      exact (zpow_pos h0 k).ne' this
    obtain ⟨j, hj⟩ := hall y hy0
    rw [hk, hj, ← zpow_natCast, ← _root_.zpow_mul] at hy
    have := zpow_right_injective₀ h0 h1.ne hy
    exact ⟨j, by rw [this]; push_cast; ring⟩
  · rintro ⟨j, rfl⟩
    refine ⟨π ^ j, ?_⟩
    rw [hk, norm_zpow, ← zpow_natCast, ← _root_.zpow_mul]
    congr 1
    push_cast; ring

theorem eta_of_exp {F : Type} [NormedField F] {π : F} (h0 : 0 < ‖π‖) (h1 : ‖π‖ < 1)
    (hall : ∀ x : F, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k) {x : F} {k : ℤ} (hk : ‖x‖ = ‖π‖ ^ k) :
    eta x = if Even k then 1 else -1 := by
  have := sq_iff_even h0 h1 hall hk
  by_cases h : Even k
  · rw [(eta_eq_one_iff x).2 (this.2 h)]; simp [h]
  · rw [(eta_eq_neg_one_iff x).2 (fun h' => h (this.1 h'))]; simp [h]

theorem eta_mul (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] (x y : F)
    (hx : x ≠ 0) (hy : y ≠ 0) : eta (x * y) = eta x * eta y := by
  obtain ⟨π, h0, h1, hall⟩ := exists_unif F
  obtain ⟨k, hk⟩ := hall x hx
  obtain ⟨l, hl⟩ := hall y hy
  have hkl : ‖x * y‖ = ‖π‖ ^ (k + l) := by rw [norm_mul, hk, hl, zpow_add₀ h0.ne']
  rw [eta_of_exp h0 h1 hall hk, eta_of_exp h0 h1 hall hl, eta_of_exp h0 h1 hall hkl]
  by_cases ek : Even k <;> by_cases el : Even l <;> simp [ek, el, Int.even_add]

theorem eta_of_norm_eq {F : Type} [NormedField F] {x y : F} (h : ‖x‖ = ‖y‖) : eta x = eta y := by
  have e : (∃ z : F, ‖x‖ = ‖z‖ ^ 2) ↔ (∃ z : F, ‖y‖ = ‖z‖ ^ 2) := by rw [h]
  by_cases hh : ∃ z : F, ‖x‖ = ‖z‖ ^ 2
  · rw [(eta_eq_one_iff x).2 hh, (eta_eq_one_iff y).2 (e.1 hh)]
  · rw [(eta_eq_neg_one_iff x).2 hh, (eta_eq_neg_one_iff y).2 (fun h' => hh (e.2 h'))]

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], (∀ x y : F, x ≠ 0 → y ≠ 0 → eta (x * y) = eta x * eta y) ∧ (∀ x : F, ‖x‖ = 1 → eta x = 1) ∧ (∀ x : F, x ≠ 0 → (eta x = 1 ↔ ∃ v : E, v * star v = algebraMap F E x)) ∧ IsLocallyConstant (fun x : {x : F // x ≠ 0} => eta x.1) := by
  intro F E _ _ _ _ hU
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : LocallyCompactSpace F := hU.lcF
  refine ⟨fun x y hx hy => eta_mul F x y hx hy, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · exact (eta_eq_one_iff x).2 ⟨1, by rw [hx, norm_one, one_pow]⟩
  · rw [eta_eq_one_iff]
    constructor
    · rintro ⟨y, hy⟩
      have hy0 : y ≠ 0 := by
        rintro rfl
        exact hx (norm_eq_zero.1 (by simpa using hy))
      obtain ⟨v, hv⟩ := GlobalTheory.T.exists_mul_star_eq_of_norm_one_unramifiedQuadratic F E (x / y ^ 2) (by rw [norm_div, norm_pow, hy, div_self (by positivity)])
      refine ⟨v * algebraMap F E y, ?_⟩
      rw [star_mul', hU.star_fix y]
      calc v * algebraMap F E y * (star v * algebraMap F E y)
          = (v * star v) * algebraMap F E (y ^ 2) := by rw [map_pow]; ring
        _ = algebraMap F E x := by rw [hv, ← map_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hy0)]
    · rintro ⟨v, hv⟩
      obtain ⟨z, hz⟩ := hU.unram v
      refine ⟨z, ?_⟩
      have := congrArg norm hv
      rw [norm_algebraMap', norm_mul, hU.norm_star, hz] at this
      rw [← this, sq]
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hx : 0 < ‖x.1‖ := norm_pos_iff.2 x.2
    have hmem : {y : {x : F // x ≠ 0} | ‖y.1 - x.1‖ < ‖x.1‖} ∈ 𝓝 x := by
      have : IsOpen {y : {x : F // x ≠ 0} | ‖y.1 - x.1‖ < ‖x.1‖} :=
        isOpen_lt (continuous_norm.comp (continuous_subtype_val.sub continuous_const)) continuous_const
      exact this.mem_nhds (by simpa using hx)
    filter_upwards [hmem] with y hy
    apply eta_of_norm_eq
    have h2 : y.1 = x.1 + (y.1 - x.1) := by ring
    rw [h2, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hy), max_eq_left hy.le]

end GlobalTheory.EtaChar
