import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

namespace EulerCharacteristicLength

def prim (f : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x in (0:ℝ)..t, f x

theorem prim_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (t : ℝ) :
    HasDerivAt (prim f) (f t) t :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

theorem prim_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (prim f) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun t => (prim_hasDerivAt hf.continuous t).differentiableAt, ?_⟩
  have : deriv (prim f) = f := funext fun t => (prim_hasDerivAt hf.continuous t).deriv
  rw [this]; exact hf

theorem prim_zero_of_nonpos {f : ℝ → ℝ} (hf : ∀ x, x ≤ 0 → f x = 0) {t : ℝ} (ht : t ≤ 0) :
    prim f t = 0 := by
  unfold prim
  rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_]
  · simp
  intro x hx
  rw [uIcc_of_ge ht] at hx
  exact hf x hx.2

theorem prim_nonneg {f : ℝ → ℝ} (hf0 : ∀ x, x ≤ 0 → f x = 0) (hf : ∀ x, 0 ≤ f x) (t : ℝ) :
    0 ≤ prim f t := by
  rcases le_total t 0 with ht | ht
  · rw [prim_zero_of_nonpos hf0 ht]
  · exact intervalIntegral.integral_nonneg ht (fun x _ => hf x)

theorem prim_pos {f : ℝ → ℝ} (hc : Continuous f) (hf : ∀ x, 0 < x → 0 < f x) {t : ℝ}
    (ht : 0 < t) : 0 < prim f t :=
  intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable _ _)
    (fun x hx => hf x hx.1) ht

def P : ℝ → ℝ := prim expNegInvGlue

def sig : ℝ → ℝ := prim P

theorem rho_contDiff : ContDiff ℝ ∞ expNegInvGlue := expNegInvGlue.contDiff
theorem primitive_contDiff₂ : ContDiff ℝ ∞ P := prim_contDiff rho_contDiff
theorem sig_contDiff : ContDiff ℝ ∞ sig := prim_contDiff primitive_contDiff₂
theorem primitive_hasDerivAt (t : ℝ) : HasDerivAt P (expNegInvGlue t) t :=
  prim_hasDerivAt rho_contDiff.continuous t
theorem sig_hasDerivAt (t : ℝ) : HasDerivAt sig (P t) t := prim_hasDerivAt primitive_contDiff₂.continuous t
theorem P_zero {t : ℝ} (ht : t ≤ 0) : P t = 0 :=
  prim_zero_of_nonpos (fun _ hx => expNegInvGlue.zero_of_nonpos hx) ht
theorem sig_zero {t : ℝ} (ht : t ≤ 0) : sig t = 0 := prim_zero_of_nonpos (fun _ hx => P_zero hx) ht
theorem P_nonneg (t : ℝ) : 0 ≤ P t :=
  prim_nonneg (fun _ hx => expNegInvGlue.zero_of_nonpos hx) expNegInvGlue.nonneg t
theorem sig_nonneg (t : ℝ) : 0 ≤ sig t := prim_nonneg (fun _ hx => P_zero hx) P_nonneg t
theorem twoPow_pos {t : ℝ} (ht : 0 < t) : 0 < P t :=
  prim_pos rho_contDiff.continuous (fun _ hx => expNegInvGlue.pos_of_pos hx) ht
theorem sig_pos {t : ℝ} (ht : 0 < t) : 0 < sig t :=
  prim_pos primitive_contDiff₂.continuous (fun _ hx => twoPow_pos hx) ht
theorem P_mono : Monotone P :=
  monotone_of_deriv_nonneg (fun t => (primitive_hasDerivAt t).differentiableAt)
    (fun t => by rw [(primitive_hasDerivAt t).deriv]; exact expNegInvGlue.nonneg t)
theorem sig_mono : Monotone sig :=
  monotone_of_deriv_nonneg (fun t => (sig_hasDerivAt t).differentiableAt)
    (fun t => by rw [(sig_hasDerivAt t).deriv]; exact P_nonneg t)

def Fs (c : ℕ → ℝ) (a : ℝ) (m : ℕ) (t : ℝ) : ℝ := ∑ k ∈ Finset.range m, c k * sig (t - (a + k))
def Fs1 (c : ℕ → ℝ) (a : ℝ) (m : ℕ) (t : ℝ) : ℝ := ∑ k ∈ Finset.range m, c k * P (t - (a + k))
def Fs2 (c : ℕ → ℝ) (a : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range m, c k * expNegInvGlue (t - (a + k))

theorem Fs_hasDerivAt (c : ℕ → ℝ) (a : ℝ) (m : ℕ) (t : ℝ) :
    HasDerivAt (Fs c a m) (Fs1 c a m t) t := by
  unfold Fs Fs1
  apply HasDerivAt.fun_sum
  intro k _
  exact (HasDerivAt.comp_sub_const t (a + k) (sig_hasDerivAt _)).const_mul (c k)

theorem Fs1_hasDerivAt (c : ℕ → ℝ) (a : ℝ) (m : ℕ) (t : ℝ) :
    HasDerivAt (Fs1 c a m) (Fs2 c a m t) t := by
  unfold Fs1 Fs2
  apply HasDerivAt.fun_sum
  intro k _
  exact (HasDerivAt.comp_sub_const t (a + k) (primitive_hasDerivAt _)).const_mul (c k)

theorem Fs_contDiff (c : ℕ → ℝ) (a : ℝ) (m : ℕ) : ContDiff ℝ ∞ (Fs c a m) := by
  unfold Fs
  exact ContDiff.sum fun k _ => contDiff_const.mul (sig_contDiff.comp (contDiff_id.sub contDiff_const))

def chiF (c : ℕ → ℝ) (a : ℝ) (t : ℝ) : ℝ := ∑' k : ℕ, c k * sig (t - (a + k))

theorem chiF_eq {c : ℕ → ℝ} {a t : ℝ} {m : ℕ} (ht : t < a + m) : chiF c a t = Fs c a m t := by
  unfold chiF Fs
  apply tsum_eq_sum
  intro k hk
  rw [Finset.mem_range, not_lt] at hk
  have : (m:ℝ) ≤ k := by exact_mod_cast hk
  rw [sig_zero (by linarith), mul_zero]

theorem chiF_eventuallyEq {c : ℕ → ℝ} {a t : ℝ} {m : ℕ} (ht : t < a + m) :
    chiF c a =ᶠ[𝓝 t] Fs c a m :=
  Filter.mem_of_superset (isOpen_Iio.mem_nhds ht) fun _ hs => chiF_eq hs

theorem deriv_chiF {c : ℕ → ℝ} {a t : ℝ} {m : ℕ} (ht : t < a + m) :
    deriv (chiF c a) t = Fs1 c a m t := by
  rw [(chiF_eventuallyEq ht).deriv_eq, (Fs_hasDerivAt c a m t).deriv]

theorem deriv2_chiF {c : ℕ → ℝ} {a t : ℝ} {m : ℕ} (ht : t < a + m) :
    deriv (deriv (chiF c a)) t = Fs2 c a m t := by
  have h : deriv (chiF c a) =ᶠ[𝓝 t] Fs1 c a m :=
    Filter.mem_of_superset (isOpen_Iio.mem_nhds ht) fun _ hs => deriv_chiF hs
  rw [h.deriv_eq, (Fs1_hasDerivAt c a m t).deriv]

theorem exists_m (a t : ℝ) : ∃ m : ℕ, t < a + m := by
  obtain ⟨m, hm⟩ := exists_nat_gt (t - a)
  exact ⟨m, by linarith⟩

theorem chiF_contDiff (c : ℕ → ℝ) (a : ℝ) : ContDiff ℝ ∞ (chiF c a) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  obtain ⟨m, hm⟩ := exists_m a t
  exact (Fs_contDiff c a m).contDiffAt.congr_of_eventuallyEq (chiF_eventuallyEq hm)

end EulerCharacteristicLength

open EulerCharacteristicLength in
theorem chi : ChiStatement := by
  intro a R hR
  choose B hB using hR
  have hμpos : 0 < min (sig 1) (P 1) := lt_min (sig_pos one_pos) (twoPow_pos one_pos)
  set μ := min (sig 1) (P 1) with hμ
  set c : ℕ → ℝ := fun k => max 0 (B (a + k + 2)) / μ with hcdef
  have hc0 : ∀ k, 0 ≤ c k := fun k => div_nonneg (le_max_left _ _) hμpos.le
  refine ⟨chiF c a, chiF_contDiff c a, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have h0 : ∀ k : ℕ, c k * sig (t - (a + k)) = 0 := fun k => by
      have := k.cast_nonneg (α := ℝ)
      rw [sig_zero (by linarith), mul_zero]
    simp only [chiF, h0, tsum_zero]
  · intro t
    obtain ⟨m, hm⟩ := exists_m a t
    rw [chiF_eq hm]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hc0 k) (sig_nonneg _)
  · intro t
    obtain ⟨m, hm⟩ := exists_m a t
    rw [deriv_chiF hm]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hc0 k) (P_nonneg _)
  · intro t
    obtain ⟨m, hm⟩ := exists_m a t
    rw [deriv2_chiF hm]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hc0 k) (expNegInvGlue.nonneg _)
  · intro t ht
    set k := ⌊t - a - 1⌋₊ with hk
    have hk1 : (k:ℝ) ≤ t - a - 1 := Nat.floor_le (by linarith)
    have hk2 : t - a - 1 < k + 1 := Nat.lt_floor_add_one _
    have hm : t < a + ((k + 2 : ℕ) : ℝ) := by push_cast; linarith
    have hkm : k ∈ Finset.range (k + 2) := Finset.mem_range.2 (by omega)
    have hRB : R t ≤ B (a + k + 2) := hB (a + k + 2) ⟨t, by simp only [mem_Iic]; linarith, rfl⟩
    have hcμ : c k * μ = max 0 (B (a + k + 2)) := by
      simp only [hcdef]; field_simp
    have hs1 : 1 ≤ t - (a + k) := by linarith
    have hbase : R t ≤ c k * μ := by rw [hcμ]; exact hRB.trans (le_max_right _ _)
    constructor
    · rw [chiF_eq hm]
      refine hbase.trans ((mul_le_mul_of_nonneg_left ((min_le_left _ _).trans (sig_mono hs1))
        (hc0 k)).trans ?_)
      exact Finset.single_le_sum (f := fun k => c k * sig (t - (a + k)))
        (fun i _ => mul_nonneg (hc0 i) (sig_nonneg _)) hkm
    · rw [deriv_chiF hm]
      refine hbase.trans ((mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (P_mono hs1))
        (hc0 k)).trans ?_)
      exact Finset.single_le_sum (f := fun k => c k * P (t - (a + k)))
        (fun i _ => mul_nonneg (hc0 i) (P_nonneg _)) hkm

end

end ReciprocityTheory.L2DbarEstimates.F
