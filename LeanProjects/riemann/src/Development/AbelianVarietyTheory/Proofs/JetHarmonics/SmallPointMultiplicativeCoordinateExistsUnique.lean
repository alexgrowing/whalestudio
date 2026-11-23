import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UwEllipticFlow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RingHomPointBijective
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

noncomputable section
namespace GlobalTheory.MomOne.SmallPt
variable {q : ℕ} [Fact q.Prime]

lemma norm_pow_sub_pow {a b : ℂ_[q]} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (n : ℕ) :
    ‖a ^ (n + 1) - b ^ (n + 1)‖ ≤ r ^ n * ‖a - b‖ := by
  have hr : 0 ≤ r := (norm_nonneg a).trans ha
  induction n with
  | zero => simp
  | succ n ih =>
    have key : a ^ (n + 1 + 1) - b ^ (n + 1 + 1) =
        a * (a ^ (n + 1) - b ^ (n + 1)) + (a - b) * b ^ (n + 1) := by ring
    rw [key]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖a‖ * ‖a ^ (n + 1) - b ^ (n + 1)‖ ≤ r * (r ^ n * ‖a - b‖) :=
            mul_le_mul ha ih (norm_nonneg _) hr
        _ = r ^ (n + 1) * ‖a - b‖ := by ring
    · rw [norm_mul, norm_pow]
      calc ‖a - b‖ * ‖b‖ ^ (n + 1) ≤ ‖a - b‖ * r ^ (n + 1) := by gcongr
        _ = r ^ (n + 1) * ‖a - b‖ := mul_comm _ _

lemma summable_ev {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) {a : ℂ_[q]} (ha : ‖a‖ < 1) :
    Summable fun n => coeff n f * a ^ n := by
  have hf' : ∀ n, ‖coeff n f‖ ≤ 1 := hf
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  apply squeeze_zero_norm (a := fun n => ‖a‖ ^ n)
  · intro n
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (hf' n)
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) ha

lemma ev_zero (f : ℂ_[q]⟦X⟧) : ev f 0 = constantCoeff f := by
  unfold ev
  rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
  simp

lemma norm_ev_sub {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) {a b : ℂ_[q]} {r : ℝ} (hr : r < 1) (ha : ‖a‖ ≤ r)
    (hb : ‖b‖ ≤ r) : ‖ev f a - ev f b - coeff 1 f * (a - b)‖ ≤ r * ‖a - b‖ := by
  have hf' : ∀ n, ‖coeff n f‖ ≤ 1 := hf
  have hr0 : 0 ≤ r := (norm_nonneg a).trans ha
  have hsa := summable_ev hf (ha.trans_lt hr)
  have hsb := summable_ev hf (hb.trans_lt hr)
  set s : ℕ → ℂ_[q] := fun n => coeff n f * a ^ n - coeff n f * b ^ n with hs_def
  have hs : Summable s := hsa.sub hsb
  have hdiff : ev f a - ev f b = ∑' n, s n := by
    unfold ev; exact (hsa.tsum_sub hsb).symm
  have e0 : s 0 = 0 := by simp [hs_def]
  have e1 : s 1 = coeff 1 f * (a - b) := by simp only [hs_def, pow_one]; ring
  have key : ev f a - ev f b - coeff 1 f * (a - b) = ∑' n, s (n + 2) := by
    rw [hdiff, ← hs.sum_add_tsum_nat_add 2, Finset.sum_range_succ, Finset.sum_range_one, e0, e1]
    ring
  rw [key]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg hr0 (norm_nonneg _)) (fun n => ?_)
  simp only [hs_def]
  rw [← mul_sub, norm_mul]
  have h2 : ‖a ^ (n + 1 + 1) - b ^ (n + 1 + 1)‖ ≤ r ^ (n + 1) * ‖a - b‖ :=
    norm_pow_sub_pow ha hb (n + 1)
  have h3 : r ^ (n + 1) ≤ r := by
    simpa using pow_le_pow_of_le_one hr0 hr.le (Nat.le_add_left 1 n)
  calc ‖coeff (n + 2) f‖ * ‖a ^ (n + 2) - b ^ (n + 2)‖ ≤ 1 * (r ^ (n + 1) * ‖a - b‖) :=
        mul_le_mul (hf' _) h2 (norm_nonneg _) zero_le_one
    _ ≤ r * ‖a - b‖ := by rw [one_mul]; exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)

lemma norm_ev_sub_eq {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (h1 : ‖coeff 1 f‖ = 1) {a b : ℂ_[q]} (ha : ‖a‖ < 1)
    (hb : ‖b‖ < 1) : ‖ev f a - ev f b‖ = ‖a - b‖ := by
  by_cases hab : a = b
  · subst hab; simp
  have hr1 : max ‖a‖ ‖b‖ < 1 := max_lt ha hb
  have hD := norm_ev_sub hf hr1 (le_max_left _ _) (le_max_right _ _)
  have hpos : 0 < ‖a - b‖ := norm_pos_iff.2 (sub_ne_zero.2 hab)
  have hlin : ‖coeff 1 f * (a - b)‖ = ‖a - b‖ := by rw [norm_mul, h1, one_mul]
  have hlt : ‖ev f a - ev f b - coeff 1 f * (a - b)‖ < ‖coeff 1 f * (a - b)‖ := by
    rw [hlin]
    calc _ ≤ max ‖a‖ ‖b‖ * ‖a - b‖ := hD
      _ < 1 * ‖a - b‖ := mul_lt_mul_of_pos_right hr1 hpos
      _ = ‖a - b‖ := one_mul _
  have hsplit : ev f a - ev f b =
      coeff 1 f * (a - b) + (ev f a - ev f b - coeff 1 f * (a - b)) := by ring
  rw [hsplit, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le, hlin]

lemma exists_ev_eq {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (h0 : constantCoeff f = 0) (h1 : ‖coeff 1 f‖ = 1)
    {t : ℂ_[q]} (ht : ‖t‖ < 1) : ∃ a, ‖a‖ < 1 ∧ ev f a = t := by
  have hev0 : ev f 0 = 0 := by rw [ev_zero, h0]
  have hc : coeff 1 f ≠ 0 := by
    intro hc; rw [hc, norm_zero] at h1; exact zero_ne_one h1
  have ht0 : 0 ≤ ‖t‖ := norm_nonneg _
  have hz : ‖(0 : ℂ_[q])‖ ≤ ‖t‖ := by simp [ht0]
  have hmaps : ∀ x : ℂ_[q], ‖x‖ ≤ ‖t‖ → ‖x - (coeff 1 f)⁻¹ * (ev f x - t)‖ ≤ ‖t‖ := by
    intro x hx
    have hD := norm_ev_sub hf ht hx hz
    rw [hev0, sub_zero, sub_zero] at hD
    have e : x - (coeff 1 f)⁻¹ * (ev f x - t) =
        (coeff 1 f)⁻¹ * t + -((coeff 1 f)⁻¹ * (ev f x - coeff 1 f * x)) := by
      linear_combination (-x) * inv_mul_cancel₀ hc
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_inv, h1, inv_one, one_mul]
    · rw [norm_neg, norm_mul, norm_inv, h1, inv_one, one_mul]
      exact hD.trans (mul_le_of_le_one_right ht0 (hx.trans ht.le))
  let T : Metric.closedBall (0 : ℂ_[q]) ‖t‖ → Metric.closedBall (0 : ℂ_[q]) ‖t‖ :=
    fun x => ⟨x.1 - (coeff 1 f)⁻¹ * (ev f x.1 - t), by
      rw [Metric.mem_closedBall, dist_zero_right]
      have hx := x.2
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      exact hmaps x.1 hx⟩
  have hK : ContractingWith ‖t‖₊ T := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    · rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]; exact ht
    · have hx := x.2
      have hy := y.2
      rw [Metric.mem_closedBall, dist_zero_right] at hx hy
      rw [coe_nnnorm, Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
      show ‖(x.1 - (coeff 1 f)⁻¹ * (ev f x.1 - t)) - (y.1 - (coeff 1 f)⁻¹ * (ev f y.1 - t))‖ ≤
        ‖t‖ * ‖x.1 - y.1‖
      have e2 : (x.1 - (coeff 1 f)⁻¹ * (ev f x.1 - t)) - (y.1 - (coeff 1 f)⁻¹ * (ev f y.1 - t)) =
          -((coeff 1 f)⁻¹ * (ev f x.1 - ev f y.1 - coeff 1 f * (x.1 - y.1))) := by
        linear_combination (-(x.1 - y.1)) * inv_mul_cancel₀ hc
      rw [e2, norm_neg, norm_mul, norm_inv, h1, inv_one, one_mul]
      exact norm_ev_sub hf ht hx hy
  have : CompleteSpace (Metric.closedBall (0 : ℂ_[q]) ‖t‖) :=
    Metric.isClosed_closedBall.completeSpace_coe
  have : Nonempty (Metric.closedBall (0 : ℂ_[q]) ‖t‖) := ⟨⟨0, by simp [ht0]⟩⟩
  have hfix : T (ContractingWith.fixedPoint T hK) = ContractingWith.fixedPoint T hK :=
    ContractingWith.fixedPoint_isFixedPt hK
  obtain ⟨a, haB⟩ := ContractingWith.fixedPoint T hK
  have hval := congrArg Subtype.val hfix
  refine ⟨(ContractingWith.fixedPoint T hK).1, ?_, ?_⟩
  · have hm := (ContractingWith.fixedPoint T hK).2
    rw [Metric.mem_closedBall, dist_zero_right] at hm
    exact hm.trans_lt ht
  · have h2 : (coeff 1 f)⁻¹ * (ev f (ContractingWith.fixedPoint T hK).1 - t) = 0 := by
      have hv : (ContractingWith.fixedPoint T hK).1 - (coeff 1 f)⁻¹ *
          (ev f (ContractingWith.fixedPoint T hK).1 - t) = (ContractingWith.fixedPoint T hK).1 := hval
      linear_combination -hv
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 (inv_ne_zero hc)
    · exact sub_eq_zero.1 h3

def cub (W : WeierstrassCurve ℂ_[q]) (u : ℂ_[q]) : ℂ_[q]⟦X⟧ :=
  PowerSeries.mk fun n => if n = 1 then 1 - (W.a₁ * u + W.a₂ * u ^ 2) else
    if n = 2 then -(W.a₃ + W.a₄ * u) else if n = 3 then -W.a₆ else 0

lemma ev_cub (W : WeierstrassCurve ℂ_[q]) (u w : ℂ_[q]) :
    ev (cub W u) w = w - (W.a₁ * u * w + W.a₂ * u ^ 2 * w + W.a₃ * w ^ 2 + W.a₄ * u * w ^ 2 +
      W.a₆ * w ^ 3) := by
  unfold ev cub
  rw [tsum_eq_sum (s := {1, 2, 3})]
  · simp [Finset.sum_insert, coeff_mk]
    ring
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [coeff_mk, hn.1, hn.2.1, hn.2.2]

variable {M : Mdl q}

lemma norm_coeff_one_cub (h : M.Ok) {u : ℂ_[q]} (hu : ‖u‖ < 1) : ‖coeff 1 (cub M.W u)‖ = 1 := by
  unfold Mdl.Ok at h
  obtain ⟨-, h1, h2, -, -, -, -, -, -⟩ := h
  have hs : ‖M.W.a₁ * u + M.W.a₂ * u ^ 2‖ < 1 := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) h1).trans_lt hu
    · rw [norm_mul, norm_pow]
      exact (mul_le_of_le_one_left (by positivity) h2).trans_lt
        (pow_lt_one₀ (norm_nonneg _) hu two_ne_zero)
  rw [cub, coeff_mk, if_pos rfl]
  have hne : ‖(1 : ℂ_[q])‖ ≠ ‖-(M.W.a₁ * u + M.W.a₂ * u ^ 2)‖ := by
    rw [norm_one, norm_neg]; exact hs.ne'
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one, norm_neg,
    max_eq_left hs.le]

lemma bd_cub (h : M.Ok) {u : ℂ_[q]} (hu : ‖u‖ < 1) : Bd 1 (cub M.W u) := by
  have h1 := norm_coeff_one_cub h hu
  unfold Mdl.Ok at h
  obtain ⟨-, -, -, ha3, ha4, ha6, -, -, -⟩ := h
  unfold Bd
  intro n
  by_cases e1 : n = 1
  · subst e1; exact h1.le
  by_cases e2 : n = 2
  · subst e2
    rw [cub, coeff_mk, if_neg (by norm_num), if_pos rfl, norm_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha3 ?_)
    rw [norm_mul]; exact mul_le_one₀ ha4 (norm_nonneg _) hu.le
  by_cases e3 : n = 3
  · subst e3
    rw [cub, coeff_mk, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl, norm_neg]
    exact ha6
  · rw [cub, coeff_mk, if_neg e1, if_neg e2, if_neg e3, norm_zero]; exact zero_le_one

private lemma one_lt_norm_y_of_small_of_not_mem (h : M.Ok) {p : ℂ} (hp : M.Small p) (hL : p ∉ M.L.lattice) :
    1 < ‖M.ι (M.y p)‖ := by
  unfold Mdl.Small at hp
  have hx : 1 < ‖M.ι (M.x p)‖ := hp.resolve_left hL
  exact hx.trans (UW.norm_x_lt M h hL hx)

lemma ev_cub_small (h : M.Ok) {p : ℂ} (hp : M.Small p) :
    ev (cub M.W (M.ι (M.u p))) (M.ι (M.w p)) = M.ι (M.u p) ^ 3 := by
  rw [ev_cub]
  unfold Mdl.u Mdl.w
  by_cases hL : p ∈ M.L.lattice
  · simp [hL]
  · simp only [hL, if_false]
    have hY := one_lt_norm_y_of_small_of_not_mem h hp hL
    have hy' : M.ι (M.y p) ≠ 0 := fun e => by rw [e, norm_zero] at hY; linarith
    have E := congrArg M.ι (UW.equation M h hL)
    simp only [map_add, map_mul, map_pow, RingEquiv.apply_symm_apply] at E
    simp only [map_div₀, map_neg, map_one]
    field_simp
    linear_combination (-1 : ℂ_[q]) * E

private lemma norm_u_w_lt_one_and_w_eq_zero_iff_of_small (h : M.Ok) {p : ℂ} (hp : M.Small p) :
    ‖M.ι (M.u p)‖ < 1 ∧ ‖M.ι (M.w p)‖ < 1 ∧ (M.w p = 0 ↔ p ∈ M.L.lattice) := by
  by_cases hL : p ∈ M.L.lattice
  · have hu : M.u p = 0 := by unfold Mdl.u; simp [hL]
    have hw : M.w p = 0 := by unfold Mdl.w; simp [hL]
    simp [hu, hw, hL]
  · have hY := one_lt_norm_y_of_small_of_not_mem h hp hL
    have hp2 := hp
    unfold Mdl.Small at hp2
    have hx : 1 < ‖M.ι (M.x p)‖ := hp2.resolve_left hL
    have hxy := UW.norm_x_lt M h hL hx
    have hY0 : 0 < ‖M.ι (M.y p)‖ := zero_lt_one.trans hY
    have hu : M.u p = -M.x p / M.y p := by unfold Mdl.u; simp [hL]
    have hw : M.w p = -1 / M.y p := by unfold Mdl.w; simp [hL]
    have hy0 : M.y p ≠ 0 := fun e => by rw [e, map_zero, norm_zero] at hY; linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [hu, map_div₀, map_neg, norm_div, norm_neg, div_lt_one hY0]; exact hxy
    · rw [hw, map_div₀, map_neg, map_one, norm_div, norm_neg, norm_one, div_lt_one hY0]; exact hY
    · rw [hw]; simp [hy0, hL]

lemma sub_mem_of_u_eq (h : M.Ok) {p p' : ℂ} (hp : M.Small p) (hp' : M.Small p')
    (e : M.u p = M.u p') : p - p' ∈ M.L.lattice := by
  classical
  obtain ⟨-, hw1, hwL1⟩ := norm_u_w_lt_one_and_w_eq_zero_iff_of_small h hp
  obtain ⟨hu2, hw2, hwL2⟩ := norm_u_w_lt_one_and_w_eq_zero_iff_of_small h hp'
  have hU : M.ι (M.u p) = M.ι (M.u p') := by rw [e]
  have hev1 := ev_cub_small h hp
  have hev2 := ev_cub_small h hp'
  rw [hU] at hev1
  have hiso := norm_ev_sub_eq (bd_cub h hu2) (norm_coeff_one_cub h hu2) hw1 hw2
  rw [hev1, hev2, sub_self, norm_zero, eq_comm, norm_eq_zero, sub_eq_zero] at hiso
  have hW : M.w p = M.w p' := M.ι.injective hiso
  by_cases hL : p ∈ M.L.lattice
  · have hL' : p' ∈ M.L.lattice := hwL2.1 (by rw [← hW]; exact hwL1.2 hL)
    exact sub_mem hL hL'
  · have hL' : p' ∉ M.L.lattice := fun h' => hL (hwL1.1 (hW.trans (hwL2.2 h')))
    have hy0 : M.y p' ≠ 0 := fun e0 => by
      have := one_lt_norm_y_of_small_of_not_mem h hp' hL'
      rw [e0, map_zero, norm_zero] at this; linarith
    have hy : M.y p = M.y p' := by
      have h0 := hW
      unfold Mdl.w at h0
      simp only [hL, hL', if_false] at h0
      rw [neg_div, neg_div, neg_inj, one_div, one_div, inv_inj] at h0
      exact h0
    have hx : M.x p = M.x p' := by
      have h0 := e
      unfold Mdl.u at h0
      simp only [hL, hL', if_false] at h0
      rw [hy, div_left_inj' hy0, neg_inj] at h0
      exact h0
    obtain ⟨φ, -, hker, hφ⟩ := Mdl.exists_pointHom q M h
    obtain ⟨h1, e1⟩ := hφ p hL
    obtain ⟨h2, e2⟩ := hφ p' hL'
    have hφ0 : φ (p - p') = 0 := by
      rw [map_sub, e1, e2, sub_eq_zero, WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨by rw [hx], by rw [hy]⟩
    exact (hker _).1 hφ0

lemma exists_small (h : M.Ok) {u : ℂ_[q]} (hu : ‖u‖ < 1) : ∃ p, M.Small p ∧ u = M.ι (M.u p) := by
  classical
  have hf := bd_cub h hu
  have hc1 := norm_coeff_one_cub h hu
  have h0 : constantCoeff (cub M.W u) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, cub, coeff_mk]; simp
  have hu3 : ‖u ^ 3‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hu (by norm_num)
  obtain ⟨w, hw, hev⟩ := exists_ev_eq hf h0 hc1 hu3
  rw [ev_cub] at hev
  by_cases hw0 : w = 0
  · subst hw0
    have hu0 : u = 0 := by
      have h3 : u ^ 3 = 0 := by rw [← hev]; ring
      exact (pow_eq_zero_iff (by norm_num)).1 h3
    refine ⟨0, by unfold Mdl.Small; exact Or.inl (zero_mem _), ?_⟩
    unfold Mdl.u
    simp [hu0]
  · have hOk := h
    unfold Mdl.Ok at hOk
    obtain ⟨-, ha1, ha2, ha3, ha4, ha6, hΔ, -, -⟩ := hOk
    have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
    have hrel : w = u ^ 3 + M.W.a₁ * u * w + M.W.a₂ * u ^ 2 * w + M.W.a₃ * w ^ 2 +
        M.W.a₄ * u * w ^ 2 + M.W.a₆ * w ^ 3 := by linear_combination hev
    have hwu : ‖w‖ < ‖u‖ := by
      by_contra hle
      push Not at hle
      have hw1 : ‖w‖ ≤ 1 := hw.le
      have hu1 : ‖u‖ ≤ 1 := hu.le
      have add_le : ∀ x y : ℂ_[q], ‖x‖ ≤ ‖w‖ ^ 2 → ‖y‖ ≤ ‖w‖ ^ 2 → ‖x + y‖ ≤ ‖w‖ ^ 2 :=
        fun x y hx hy => (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
      have t1 : ‖u ^ 3‖ ≤ ‖w‖ ^ 2 := by
        rw [norm_pow]
        calc ‖u‖ ^ 3 ≤ ‖w‖ ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hle 3
          _ = ‖w‖ * ‖w‖ ^ 2 := by ring
          _ ≤ 1 * ‖w‖ ^ 2 := by gcongr
          _ = ‖w‖ ^ 2 := one_mul _
      have t2 : ‖M.W.a₁ * u * w‖ ≤ ‖w‖ ^ 2 := by
        rw [norm_mul, norm_mul]
        calc ‖M.W.a₁‖ * ‖u‖ * ‖w‖ ≤ 1 * ‖w‖ * ‖w‖ := by gcongr
          _ = ‖w‖ ^ 2 := by ring
      have t3 : ‖M.W.a₂ * u ^ 2 * w‖ ≤ ‖w‖ ^ 2 := by
        rw [norm_mul, norm_mul, norm_pow]
        calc ‖M.W.a₂‖ * ‖u‖ ^ 2 * ‖w‖ ≤ 1 * ‖w‖ ^ 2 * 1 := by gcongr
          _ = ‖w‖ ^ 2 := by ring
      have t4 : ‖M.W.a₃ * w ^ 2‖ ≤ ‖w‖ ^ 2 := by
        rw [norm_mul, norm_pow]
        calc ‖M.W.a₃‖ * ‖w‖ ^ 2 ≤ 1 * ‖w‖ ^ 2 := by gcongr
          _ = ‖w‖ ^ 2 := one_mul _
      have t5 : ‖M.W.a₄ * u * w ^ 2‖ ≤ ‖w‖ ^ 2 := by
        rw [norm_mul, norm_mul, norm_pow]
        calc ‖M.W.a₄‖ * ‖u‖ * ‖w‖ ^ 2 ≤ 1 * 1 * ‖w‖ ^ 2 := by gcongr
          _ = ‖w‖ ^ 2 := by ring
      have t6 : ‖M.W.a₆ * w ^ 3‖ ≤ ‖w‖ ^ 2 := by
        rw [norm_mul, norm_pow]
        calc ‖M.W.a₆‖ * ‖w‖ ^ 3 = ‖M.W.a₆‖ * ‖w‖ * ‖w‖ ^ 2 := by ring
          _ ≤ 1 * 1 * ‖w‖ ^ 2 := by gcongr
          _ = ‖w‖ ^ 2 := by ring
      have hb := add_le _ _ (add_le _ _ (add_le _ _ (add_le _ _ (add_le _ _ t1 t2) t3) t4) t5) t6
      rw [← hrel] at hb
      nlinarith
    have hΔ0 : M.W.Δ ≠ 0 := by
      intro e; rw [e, norm_zero] at hΔ; exact zero_ne_one hΔ
    have heq : M.W.toAffine.Equation (u / w) (-1 / w) := by
      rw [WeierstrassCurve.Affine.equation_iff]
      field_simp
      linear_combination hev
    have hns := (M.W.toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ0).1 heq
    obtain ⟨φ, hsurj, hker, hφ⟩ := Mdl.exists_pointHom q M h
    obtain ⟨z, hz⟩ := hsurj (WeierstrassCurve.Affine.Point.some (u / w) (-1 / w) hns)
    have hzL : z ∉ M.L.lattice := fun hz' => by
      rw [(hker z).2 hz'] at hz; cases hz
    obtain ⟨hz1, hz2⟩ := hφ z hzL
    rw [hz2, WeierstrassCurve.Affine.Point.some.injEq] at hz
    refine ⟨z, ?_, ?_⟩
    · unfold Mdl.Small
      right
      rw [hz.1, norm_div]
      exact (one_lt_div hwpos).2 hwu
    · unfold Mdl.u
      rw [if_neg hzL, map_div₀, map_neg, hz.1, hz.2]
      field_simp

lemma small_add {p l : ℂ} (hl : l ∈ M.L.lattice) (hp : M.Small p) : M.Small (p + l) := by
  unfold Mdl.Small at *
  by_cases hpL : p ∈ M.L.lattice
  · exact Or.inl (add_mem hpL hl)
  · right
    rw [UW.x_add M hl p]
    exact hp.resolve_left hpL

private lemma u_add_lattice {l : ℂ} (hl : l ∈ M.L.lattice) (p : ℂ) : M.u (p + l) = M.u p := by
  unfold Mdl.u
  by_cases hpL : p ∈ M.L.lattice
  · simp [hpL, add_mem hpL hl]
  · have hpl : p + l ∉ M.L.lattice := fun h' => hpL (by simpa using sub_mem h' hl)
    simp only [hpL, hpl, if_false, UW.x_add M hl p, UW.y_add M hl p]

theorem at_exists_unique : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), M.MChart ω → (∀ ζ : ℂ_[q], ‖ζ - 1‖ < 1 → ∃ p, M.At ω ζ p) ∧ (∀ p, M.Small p → ∃ ζ, M.At ω ζ p) ∧ (∀ ζ ζ' p, M.At ω ζ p → M.At ω ζ' p → ζ = ζ') ∧ (∀ ζ p p', M.At ω ζ p → (M.At ω ζ p' ↔ p - p' ∈ M.L.lattice)) ∧ M.At ω 1 0 := by
  intro q _ M ω hω
  have hch := hω
  unfold Mdl.MChart Mdl.Chart at hch
  obtain ⟨h, hℓ0, hbd, hc1⟩ := hch
  have hu0 : M.u 0 = 0 := by unfold Mdl.u; simp [zero_mem]
  have hg0 : constantCoeff (hat M.ι (C ω * logS) M.u) = 0 := by
    rw [(TaylorRead.hat_laws q M.ι _ hℓ0).2.2.2.1 M.u, hu0, map_zero]
  have hev0 : ev (hat M.ι (C ω * logS) M.u) 0 = 0 := by rw [ev_zero, hg0]
  have hAt : ∀ ζ p, M.At ω ζ p ↔ M.Small p ∧ ‖ζ - 1‖ < 1 ∧
      ev (hat M.ι (C ω * logS) M.u) (ζ - 1) = M.ι (M.u p) := fun ζ p => Iff.rfl
  have hnorm : ∀ a : ℂ_[q], ‖a‖ < 1 → ‖ev (hat M.ι (C ω * logS) M.u) a‖ = ‖a‖ := fun a ha => by
    have := norm_ev_sub_eq hbd hc1 ha (by simp : ‖(0 : ℂ_[q])‖ < 1)
    rwa [hev0, sub_zero, sub_zero] at this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ζ hζ
    have ht : ‖ev (hat M.ι (C ω * logS) M.u) (ζ - 1)‖ < 1 := by rw [hnorm _ hζ]; exact hζ
    obtain ⟨p, hp, hpu⟩ := exists_small h ht
    exact ⟨p, (hAt _ _).2 ⟨hp, hζ, hpu⟩⟩
  · intro p hp
    obtain ⟨hu1, -, -⟩ := norm_u_w_lt_one_and_w_eq_zero_iff_of_small h hp
    obtain ⟨a, ha, hea⟩ := exists_ev_eq hbd hg0 hc1 hu1
    refine ⟨a + 1, (hAt _ _).2 ⟨hp, by rw [add_sub_cancel_right]; exact ha, ?_⟩⟩
    rw [add_sub_cancel_right]; exact hea
  · intro ζ ζ' p h1 h2
    obtain ⟨-, hζ1, he1⟩ := (hAt _ _).1 h1
    obtain ⟨-, hζ2, he2⟩ := (hAt _ _).1 h2
    have := norm_ev_sub_eq hbd hc1 hζ1 hζ2
    rw [he1, he2, sub_self, norm_zero, eq_comm, norm_eq_zero, sub_eq_zero, sub_left_inj] at this
    exact this
  · intro ζ p p' h1
    obtain ⟨hp, hζ, he⟩ := (hAt _ _).1 h1
    constructor
    · intro h2
      obtain ⟨hp', -, he'⟩ := (hAt _ _).1 h2
      exact sub_mem_of_u_eq h hp hp' (M.ι.injective (he.symm.trans he'))
    · intro hd
      have hl : p' - p ∈ M.L.lattice := by simpa using neg_mem hd
      have hp' : M.Small p' := by simpa using small_add hl hp
      refine (hAt _ _).2 ⟨hp', hζ, ?_⟩
      rw [he, ← u_add_lattice hl p, add_sub_cancel]
  · refine (hAt _ _).2 ⟨by unfold Mdl.Small; exact Or.inl (zero_mem _), by simp, ?_⟩
    rw [sub_self, hev0, hu0, map_zero]

end GlobalTheory.MomOne.SmallPt
