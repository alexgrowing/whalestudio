import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap

open GlobalTheory.BK PowerSeries Filter Topology

namespace GlobalTheory.BK.HatInj

def LastMax (w : ℕ → ℝ) (d : ℕ) : Prop := (∀ n, w n ≤ w d) ∧ ∀ n, d < n → w n < w d

theorem LastMax.unique {w : ℕ → ℝ} {d d' : ℕ} (h : LastMax w d) (h' : LastMax w d') : d = d' := by
  rcases lt_trichotomy d d' with hlt | heq | hgt
  · exact absurd (h.2 d' hlt) (not_lt.mpr (h'.1 d))
  · exact heq
  · exact absurd (h'.2 d hgt) (not_lt.mpr (h.1 d'))

theorem exists_lastMax {w : ℕ → ℝ} (hw : Tendsto w atTop (𝓝 0)) {n₀ : ℕ} (h₀ : 0 < w n₀) :
    ∃ d, LastMax w d := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hw.eventually (gt_mem_nhds h₀))
  have hn₀ : n₀ < N := by
    by_contra hc
    exact lt_irrefl _ (hN n₀ (not_lt.mp hc))
  obtain ⟨a, ha, hmax⟩ := (Finset.range N).exists_max_image w ⟨n₀, Finset.mem_range.mpr hn₀⟩
  have hbig : ∀ n, N ≤ n → w n < w a := fun n hn =>
    (hN n hn).trans_le (hmax n₀ (Finset.mem_range.mpr hn₀))
  let T := (Finset.range N).filter (fun n => w n = w a)
  have hTne : T.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  have hda : w (T.max' hTne) = w a := (Finset.mem_filter.mp (T.max'_mem hTne)).2
  refine ⟨T.max' hTne, fun n => ?_, fun n hn => ?_⟩
  · rw [hda]
    rcases lt_or_ge n N with hnN | hnN
    · exact hmax n (Finset.mem_range.mpr hnN)
    · exact (hbig n hnN).le
  · rw [hda]
    rcases lt_or_ge n N with hnN | hnN
    · refine lt_of_le_of_ne (hmax n (Finset.mem_range.mpr hnN)) fun heq => ?_
      have hT : n ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnN, heq⟩
      exact absurd (T.le_max' n hT) (not_le.mpr hn)
    · exact hbig n hnN
private theorem coeff_E_mul' {K : Type} [NormedField K] [IsUltrametricDist K] (l e : ℕ)
    (h : K⟦X⟧) (n : ℕ) :
    coeff n (E K l e * h) = (if e ≤ n then coeff (n - e) h else 0) + (l : K) * coeff n h := by
  rw [E, add_mul, map_add, coeff_X_pow_mul', ← map_natCast (C : K →+* K⟦X⟧) l, coeff_C_mul]

variable {K : Type} [NormedField K] [IsUltrametricDist K] (l e : ℕ) [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e]

theorem lastMax_E_mul {h : K⟦X⟧} {d : ℕ}
    (H : LastMax (fun n => ‖coeff n h‖ * rad l (1 / e) ^ n) d) :
    LastMax (fun n => ‖coeff n (E K l e * h)‖ * rad l (1 / e) ^ n) (d + e) := by
  have hr : 0 < rad l (1 / (e : ℝ)) := rad_pos l _
  have hre : rad l (1 / (e : ℝ)) ^ e = ‖(l : K)‖ := rad_pow l e
  have hl : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (l_ne_zero (K := K) l)
  have he : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
  have hlow : ∀ n, n < e → ‖coeff n (E K l e * h)‖ * rad l (1 / (e : ℝ)) ^ n =
      ‖(l : K)‖ * (‖coeff n h‖ * rad l (1 / (e : ℝ)) ^ n) := by
    intro n hn
    rw [coeff_E_mul', if_neg (not_le.mpr hn), zero_add, norm_mul]
    ring
  have hhigh : ∀ k, ‖coeff (k + e) (E K l e * h)‖ * rad l (1 / (e : ℝ)) ^ (k + e) ≤
      max (‖(l : K)‖ * (‖coeff k h‖ * rad l (1 / (e : ℝ)) ^ k))
        (‖(l : K)‖ * (‖coeff (k + e) h‖ * rad l (1 / (e : ℝ)) ^ (k + e))) := by
    intro k
    rw [coeff_E_mul', if_pos (Nat.le_add_left e k), Nat.add_sub_cancel]
    calc ‖coeff k h + (l : K) * coeff (k + e) h‖ * rad l (1 / (e : ℝ)) ^ (k + e)
        ≤ max ‖coeff k h‖ ‖(l : K) * coeff (k + e) h‖ * rad l (1 / (e : ℝ)) ^ (k + e) :=
          mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (pow_nonneg hr.le _)
      _ = _ := by
          rw [max_mul_of_nonneg _ _ (pow_nonneg hr.le _)]
          congr 1
          · rw [pow_add, hre]; ring
          · rw [norm_mul]; ring
  have htop : ‖coeff (d + e) (E K l e * h)‖ * rad l (1 / (e : ℝ)) ^ (d + e) =
      ‖(l : K)‖ * (‖coeff d h‖ * rad l (1 / (e : ℝ)) ^ d) := by
    rw [coeff_E_mul', if_pos (Nat.le_add_left e d), Nat.add_sub_cancel]
    have hsmall : ‖(l : K) * coeff (d + e) h‖ < ‖coeff d h‖ := by
      have hlt := mul_lt_mul_of_pos_left (H.2 (d + e) (by omega)) hl
      refine lt_of_mul_lt_mul_right ?_ (pow_pos hr (d + e)).le
      calc ‖(l : K) * coeff (d + e) h‖ * rad l (1 / (e : ℝ)) ^ (d + e)
          = ‖(l : K)‖ * (‖coeff (d + e) h‖ * rad l (1 / (e : ℝ)) ^ (d + e)) := by
            rw [norm_mul]; ring
        _ < ‖(l : K)‖ * (‖coeff d h‖ * rad l (1 / (e : ℝ)) ^ d) := hlt
        _ = ‖coeff d h‖ * rad l (1 / (e : ℝ)) ^ (d + e) := by rw [pow_add, hre]; ring
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hsmall.ne', max_eq_left hsmall.le,
      pow_add, hre]
    ring
  refine ⟨fun n => ?_, fun n hn => ?_⟩
  · show ‖coeff n (E K l e * h)‖ * rad l (1 / (e : ℝ)) ^ n ≤ ‖coeff (d + e) (E K l e * h)‖ * rad l (1 / (e : ℝ)) ^ (d + e)
    rw [htop]
    rcases lt_or_ge n e with hne | hne
    · rw [hlow n hne]
      exact mul_le_mul_of_nonneg_left (H.1 n) hl.le
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hne
      exact (hhigh k).trans (max_le (mul_le_mul_of_nonneg_left (H.1 k) hl.le)
        (mul_le_mul_of_nonneg_left (H.1 (k + e)) hl.le))
  · show ‖coeff n (E K l e * h)‖ * rad l (1 / (e : ℝ)) ^ n < ‖coeff (d + e) (E K l e * h)‖ * rad l (1 / (e : ℝ)) ^ (d + e)
    rw [htop]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (show e ≤ n by omega)
    exact (hhigh k).trans_lt (max_lt (mul_lt_mul_of_pos_left (H.2 k (by omega)) hl)
      (mul_lt_mul_of_pos_left (H.2 (k + e) (by omega)) hl))

theorem lastMax_E_pow_mul {h : K⟦X⟧} {d : ℕ}
    (H : LastMax (fun n => ‖coeff n h‖ * rad l (1 / e) ^ n) d) (m : ℕ) :
    LastMax (fun n => ‖coeff n (E K l e ^ m * h)‖ * rad l (1 / e) ^ n) (d + m * e) := by
  induction m with
  | zero => simpa using H
  | succ m ih =>
    have h' := lastMax_E_mul l e ih
    rw [← mul_assoc, ← pow_succ'] at h'
    have hidx : d + (m + 1) * e = d + m * e + e := by ring
    rw [hidx]
    exact h'

theorem exists_lastMax_of_mem {O : Type} [CommRing O] [Algebra O K] [IsUnitBall O K] {h : K⟦X⟧}
    (hh : h ∈ Rpi O K l e) (h0 : h ≠ 0) :
    ∃ d, LastMax (fun n => ‖coeff n h‖ * rad l (1 / e) ^ n) d := by
  have hmem : Tendsto (fun n => ‖coeff n h‖ * rad l (1 / (e : ℝ)) ^ n) atTop (𝓝 0) :=
    mem_R.mp (show h ∈ R O K l (1 / (e : ℝ)) from hh)
  obtain ⟨n₀, hn₀⟩ : ∃ n, coeff n h ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (PowerSeries.ext fun n => by simpa using hc n)
  exact exists_lastMax hmem (mul_pos (norm_pos_iff.mpr hn₀) (pow_pos (rad_pos l _) n₀))

end GlobalTheory.BK.HatInj

namespace GlobalTheory.BK

open HatInj in

theorem toHat_injective (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    [CompleteSpace K] : Function.Injective (toHat O K l e) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hdiv : ∀ m : ℕ, ∃ y : Rpi O K l e, (x : K⟦X⟧) = E K l e ^ m * y := by
    intro m
    have h1 := congrArg (AdicCompletion.evalₐ (Ideal.span {EIn l e (invL l (A O K))}) m) hx
    unfold toHat at h1
    generalize_proofs p1 p2 p3 p4 p5 p6 p7 at h1
    unfold SameJets.toCompl SameJets.jet at h1
    erw [AdicCompletion.evalₐ_liftRingHom, map_zero, RingHom.comp_apply] at h1
    have h2 := (map_eq_zero_iff _ (RingEquiv.injective _)).mp h1
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h2
    obtain ⟨y, hy⟩ := h2
    refine ⟨y, ?_⟩
    rw [← hy]
    simp [mul_comm]
  by_contra hx0
  have hx0' : (x : K⟦X⟧) ≠ 0 := fun h => hx0 (Subtype.ext h)
  obtain ⟨d, hd⟩ := exists_lastMax_of_mem (l := l) (e := e) x.2 hx0'
  obtain ⟨y, hy⟩ := hdiv (d + 1)
  have hy0 : (y : K⟦X⟧) ≠ 0 := by
    intro h
    apply hx0'
    rw [hy, h, mul_zero]
  obtain ⟨d', hd'⟩ := exists_lastMax_of_mem (l := l) (e := e) y.2 hy0
  have h3 := lastMax_E_pow_mul (l := l) (e := e) hd' (d + 1)
  rw [← hy] at h3
  have h4 := hd.unique h3
  have he : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr (NeZero.ne e)
  have h5 : d + 1 ≤ (d + 1) * e := Nat.le_mul_of_pos_right _ he
  omega

end GlobalTheory.BK
