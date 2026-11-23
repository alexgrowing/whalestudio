import Mathlib
import Formalism.IncomingBounds.IncomingBound

noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

namespace FlowDualityReindexing

variable {l d : ℕ} [NeZero d]

lemma in_reindex (x : ZMod d → ℕ → ℝ) :
    ∑ s : ZMod d, ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i =
      ∑ s : ZMod d, ∑ i ∈ oddLevels d, x s i := by
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Fintype.sum_equiv (Equiv.subRight (i : ZMod d)) _ _ (fun s => rfl)

lemma in_reindex_mul (sig : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ) :
    ∑ s : ZMod d, sig s * ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i =
      ∑ s : ZMod d, ∑ i ∈ oddLevels d, x s i * sig (s + (i : ZMod d)) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Fintype.sum_equiv (Equiv.subRight (i : ZMod d)) _ _ (fun s => ?_)
  rw [Equiv.subRight_apply, sub_add_cancel, mul_comm]

lemma cs_identity (D sig : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ) :
    ∑ s : ZMod d, D s * sig s - flowVal d x =
      ∑ s : ZMod d, sig s * (D s - ((∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) +
        (∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i))) +
      ∑ s : ZMod d, ∑ i ∈ oddLevels d,
        x s i * ((l : ℝ) ^ i * sig s + sig (s + (i : ZMod d)) - 1) := by
  have hA : ∑ s : ZMod d, sig s * (∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) =
      ∑ s : ZMod d, ∑ i ∈ oddLevels d, x s i * ((l : ℝ) ^ i * sig s) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hA, in_reindex_mul]
  simp only [mul_one]
  unfold Formalism.IncomingBounds.flowVal
  rw [show ∑ s : ZMod d, D s * sig s = ∑ s : ZMod d, sig s * D s from
    Finset.sum_congr rfl fun _ _ => mul_comm _ _]
  ring

lemma optdual_maxFlow (D sig : ZMod d → ℝ) (h : IsOptDual l d D sig) :
    maxFlow l d D = ∑ s : ZMod d, D s * sig s := by
  obtain ⟨_, h2⟩ := h
  unfold Formalism.IncomingBounds.Fnum at h2
  have : ∑ s : ZMod d, D s * (Formalism.IncomingBounds.gam l - sig s) =
      Formalism.IncomingBounds.gam l * ∑ s : ZMod d, D s - ∑ s : ZMod d, D s * sig s := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  linarith

lemma cs_zero (D sig : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ) (hx : IsFlow l d D x)
    (hs : IsDual l d sig) (heq : flowVal d x = ∑ s : ZMod d, D s * sig s) :
    (∀ s : ZMod d, sig s * (D s - ((∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) +
        (∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i))) = 0) ∧
    (∀ s : ZMod d, ∀ i ∈ oddLevels d,
        x s i * ((l : ℝ) ^ i * sig s + sig (s + (i : ZMod d)) - 1) = 0) := by
  have hid := cs_identity (l := l) D sig x
  rw [heq, sub_self] at hid
  have h1 : ∀ s : ZMod d, 0 ≤ sig s * (D s - ((∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) +
      (∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i))) :=
    fun s => mul_nonneg (hs.1 s).1 (sub_nonneg.2 (hx.2 s))
  have h2 : ∀ s : ZMod d, ∀ i ∈ oddLevels d,
      0 ≤ x s i * ((l : ℝ) ^ i * sig s + sig (s + (i : ZMod d)) - 1) :=
    fun s i hi => mul_nonneg (hx.1 s i) (sub_nonneg.2 (hs.2 s i hi))
  have hA := Finset.sum_nonneg (fun s (_ : s ∈ (Finset.univ : Finset (ZMod d))) => h1 s)
  have hB := Finset.sum_nonneg
    (fun s (_ : s ∈ (Finset.univ : Finset (ZMod d))) => Finset.sum_nonneg (h2 s))
  have hA0 := le_antisymm (by linarith) hA
  have hB0 := le_antisymm (by linarith) hB
  refine ⟨fun s => (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => h1 s)).1 hA0 s
    (Finset.mem_univ _), fun s i hi => ?_⟩
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => Finset.sum_nonneg (h2 s))).1 hB0 s
    (Finset.mem_univ _)
  exact (Finset.sum_eq_zero_iff_of_nonneg (h2 s)).1 this i hi

lemma flow_le (D : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ) (hx : IsFlow l d D x) (t : ZMod d)
    (i : ℕ) (hi : i ∈ oddLevels d) : (l : ℝ) ^ i * x t i ≤ D t := by
  have hnn : ∀ j ∈ oddLevels d, 0 ≤ (l : ℝ) ^ j * x t j :=
    fun j _ => mul_nonneg (by positivity) (hx.1 t j)
  have h1 : (l : ℝ) ^ i * x t i ≤ ∑ j ∈ oddLevels d, (l : ℝ) ^ j * x t j :=
    Finset.single_le_sum hnn hi
  have h2 : 0 ≤ ∑ j ∈ oddLevels d, x (t - (j : ZMod d)) j :=
    Finset.sum_nonneg fun j _ => hx.1 _ _
  have h3 := hx.2 t
  linarith

private theorem oddLevels_subset_image_two_mul_add_one :
    oddLevels d ⊆ (Finset.range d).image (fun k => 2 * k + 1) := by
  intro i hi
  have hlt := Finset.mem_range.1 (Finset.mem_filter.1 hi).1
  obtain ⟨k, rfl⟩ := (Finset.mem_filter.1 hi).2
  exact Finset.mem_image.2 ⟨k, Finset.mem_range.2 (by omega), rfl⟩

lemma sum_inv_pow_le (hl : 3 ≤ l) : ∑ i ∈ oddLevels d, ((l : ℝ) ^ i)⁻¹ ≤ gam l := by
  have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have hlpos : (0 : ℝ) < l := by linarith
  have hq0 : (0 : ℝ) ≤ ((l : ℝ) ^ 2)⁻¹ := by positivity
  have hq1 : ((l : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  have h2 : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have h3 : (1 : ℝ) - ((l : ℝ) ^ 2)⁻¹ ≠ 0 := by linarith
  calc ∑ i ∈ oddLevels d, ((l : ℝ) ^ i)⁻¹
        ≤ ∑ i ∈ (Finset.range d).image (fun k => 2 * k + 1), ((l : ℝ) ^ i)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg oddLevels_subset_image_two_mul_add_one
            (fun i _ _ => by positivity)
      _ = ∑ k ∈ Finset.range d, ((l : ℝ) ^ (2 * k + 1))⁻¹ := by
          refine Finset.sum_image ?_
          intro a _ b _ h
          have : 2 * a + 1 = 2 * b + 1 := h
          omega
      _ = ∑ k ∈ Finset.range d, (l : ℝ)⁻¹ * (((l : ℝ) ^ 2)⁻¹) ^ k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [pow_succ, pow_mul, mul_inv, inv_pow, mul_comm]
      _ = (l : ℝ)⁻¹ * ∑ k ∈ Finset.range d, (((l : ℝ) ^ 2)⁻¹) ^ k := by rw [Finset.mul_sum]
      _ ≤ (l : ℝ)⁻¹ * (1 / (1 - ((l : ℝ) ^ 2)⁻¹)) := by
          gcongr
          have := geom_sum_Ico_le_of_lt_one (m := 0) (n := d) hq0 hq1
          simpa using this
      _ = Formalism.IncomingBounds.gam l := by
          unfold Formalism.IncomingBounds.gam
          field_simp

private theorem one_le_of_mem_oddLevels {i : ℕ} (hi : i ∈ oddLevels d) : 1 ≤ i := by
  obtain ⟨k, rfl⟩ := (Finset.mem_filter.1 hi).2
  omega

private theorem self_le_pow_of_mem_oddLevels (hl : (1 : ℝ) ≤ l) {i : ℕ} (hi : i ∈ oddLevels d) :
    (l : ℝ) ≤ (l : ℝ) ^ i := by
  calc (l : ℝ) = (l : ℝ) ^ 1 := (pow_one _).symm
    _ ≤ (l : ℝ) ^ i := pow_le_pow_right₀ hl (one_le_of_mem_oddLevels hi)

lemma fd_part1 (hl : 3 ≤ l) (D sig : ZMod d → ℝ) (hopt : IsOptDual l d D sig) (s : ZMod d)
    (hs : 2 / (l : ℝ) ≤ sig s) (x : ZMod d → ℕ → ℝ) (hx : IsFlow l d D x)
    (hval : flowVal d x = maxFlow l d D) :
    (∀ i ∈ oddLevels d, x s i = 0) ∧ D s = ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i := by
  have hF := optdual_maxFlow D sig hopt
  obtain ⟨h1, h2⟩ := cs_zero D sig x hx hopt.1 (hval.trans hF)
  have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have hlpos : (0 : ℝ) < l := by linarith
  have hsig := hopt.1.1
  have hl2 : (l : ℝ) * (2 / l) = 2 := by field_simp
  have h2l : 2 ≤ (l : ℝ) * sig s := by
    have := mul_le_mul_of_nonneg_left hs hlpos.le
    linarith
  have hout : ∀ i ∈ oddLevels d, x s i = 0 := by
    intro i hi
    have hpow := self_le_pow_of_mem_oddLevels (l := l) (by linarith) hi
    have hred : 0 < (l : ℝ) ^ i * sig s + sig (s + (i : ZMod d)) - 1 := by
      have := mul_le_mul_of_nonneg_right hpow (hsig s).1
      linarith [(hsig (s + (i : ZMod d))).1]
    rcases mul_eq_zero.1 (h2 s i hi) with h | h
    · exact h
    · linarith
  refine ⟨hout, ?_⟩
  have hs0 : 0 < sig s := by nlinarith
  rcases mul_eq_zero.1 (h1 s) with h | h
  · linarith
  have hz : ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i = 0 :=
    Finset.sum_eq_zero fun i hi => by rw [hout i hi, mul_zero]
  rw [hz] at h
  linarith

end FlowDualityReindexing

open FlowDualityReindexing

theorem lemmaFd_of (hF : FlowAttained) (hA : LemmaFa) : LemmaFd := by
  intro l d _ hl hd hev D sig hD hopt s hs
  have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have hlpos : (0 : ℝ) < l := by linarith
  refine ⟨fun x hx hval => Formalism.IncomingBounds.FlowDualityReindexing.fd_part1 hl D sig hopt s hs x hx hval, ?_⟩
  obtain ⟨x, hx, hval⟩ := hF l d hl hd hev D hD
  have hsat := (Formalism.IncomingBounds.FlowDualityReindexing.fd_part1 hl D sig hopt s hs x hx hval).2
  have hb : D s ≤ ∑ i ∈ oddLevels d, D (s - (i : ZMod d)) / (l : ℝ) ^ i := by
    rw [hsat]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [le_div_iff₀ (pow_pos hlpos i), mul_comm]
    exact Formalism.IncomingBounds.FlowDualityReindexing.flow_le D x hx (s - (i : ZMod d)) i hi
  refine ⟨hb, fun _ => ?_⟩
  obtain ⟨s', hs'⟩ := Finite.exists_max D
  refine ⟨s', ?_⟩
  have hP : 0 < gam l := by
    unfold gam
    exact div_pos hlpos (by nlinarith)
  rw [div_le_iff₀ hP]
  calc D s ≤ ∑ i ∈ oddLevels d, D (s - (i : ZMod d)) / (l : ℝ) ^ i := hb
    _ ≤ ∑ i ∈ oddLevels d, D s' * ((l : ℝ) ^ i)⁻¹ :=
        Finset.sum_le_sum fun i _ => by
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (hs' _) (by positivity)
    _ = D s' * ∑ i ∈ oddLevels d, ((l : ℝ) ^ i)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ D s' * gam l :=
        mul_le_mul_of_nonneg_left (Formalism.IncomingBounds.FlowDualityReindexing.sum_inv_pow_le hl) (hD s')

theorem incomingBound_of (hF : FlowAttained) (hA : LemmaFa) : IncomingBound := by
  intro l d _ hl hd hev D sig hD hopt
  obtain ⟨x, hx, hval⟩ := hF l d hl hd hev D hD
  have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have hlpos : (0 : ℝ) < l := by linarith
  have hout : ∀ t : ZMod d, (l : ℝ) * ∑ i ∈ oddLevels d, x t i ≤ D t := by
    intro t
    rw [Finset.mul_sum]
    have h1 : ∑ i ∈ oddLevels d, (l : ℝ) * x t i ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x t i :=
      Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_right (_root_.Formalism.IncomingBounds.FlowDualityReindexing.self_le_pow_of_mem_oddLevels (by linarith) hi) (hx.1 t i)
    have h2 : 0 ≤ ∑ i ∈ oddLevels d, x (t - (i : ZMod d)) i :=
      Finset.sum_nonneg fun i _ => hx.1 _ _
    linarith [hx.2 t]
  calc (∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), D s)
        = ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s),
            ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i :=
          Finset.sum_congr rfl fun s hs =>
            (Formalism.IncomingBounds.FlowDualityReindexing.fd_part1 hl D sig hopt s (Finset.mem_filter.1 hs).2 x hx hval).2
      _ ≤ ∑ s : ZMod d, ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun s _ _ => Finset.sum_nonneg fun i _ => hx.1 _ _
      _ = ∑ s : ZMod d, ∑ i ∈ oddLevels d, x s i := Formalism.IncomingBounds.FlowDualityReindexing.in_reindex x
      _ ≤ ∑ s : ZMod d, D s / l :=
          Finset.sum_le_sum fun t _ => by
            rw [le_div_iff₀ hlpos, mul_comm]
            exact hout t
      _ = (∑ s : ZMod d, D s) / l := by rw [Finset.sum_div]

end Formalism.IncomingBounds
