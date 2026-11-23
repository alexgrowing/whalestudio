import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Values

variable {Ω : Type} [Field Ω]

omit [Fintype K] in
theorem isMultiHomog_sub {g h : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    (hh : IsMultiHomog h d) : IsMultiHomog (g - h) d := by
  rw [sub_eq_add_neg]
  refine isMultiHomog_add hg ?_
  intro m hm
  exact hh m (by simpa using hm)

theorem isValueAt_unique {y : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) {v w : ℂ} (hv : IsValueAt y s z v) (hw : IsValueAt y s z w) :
    v = w := by
  obtain ⟨d, g, h, hg, hh, _, heq, hz0, rfl⟩ := hv
  obtain ⟨d', g', h', hg', hh', _, heq', hz0', rfl⟩ := hw
  have hsub : IsMultiHomog (g * h' - g' * h) (d + d') := by
    refine isMultiHomog_sub (isMultiHomog_mul hg hh') ?_
    rw [add_comm]
    exact isMultiHomog_mul hg' hh
  have h0 : aeval y (g * h' - g' * h) = 0 := by
    rw [map_sub, map_mul, map_mul, heq, heq']
    ring
  have := eval_eq_zero_of_mem_mcPts hz (mem_mCoordIdeal_of_aeval_eq_zero y hsub h0)
  simp only [map_sub, map_mul, sub_eq_zero] at this
  rw [div_eq_div_iff hz0 hz0', this]

theorem isValueAt_mul {y : (Σ k, ι k) → Ω} {s t : Ω} {z : (Σ k, ι k) → ℂ} {v w : ℂ}
    (hv : IsValueAt y s z v) (hw : IsValueAt y t z w) : IsValueAt y (s * t) z (v * w) := by
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  obtain ⟨d', g', h', hg', hh', hy', heq', hz0', rfl⟩ := hw
  refine ⟨d + d', g * g', h * h', isMultiHomog_mul hg hg', isMultiHomog_mul hh hh', ?_, ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hy hy'
  · rw [map_mul, map_mul, heq, heq']; ring
  · rw [map_mul, map_mul]; exact mul_ne_zero hz0 hz0'
  · simp only [map_mul]; rw [mul_div_mul_comm]

open Classical in

def valAt (y : (Σ k, ι k) → Ω) (s : Ω) (z : (Σ k, ι k) → ℂ) : ℂ :=
  if h : ∃ v, IsValueAt y s z v then h.choose else 0

theorem valAt_eq {y : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) {v : ℂ} (hv : IsValueAt y s z v) : valAt y s z = v := by
  classical
  have h : ∃ v, IsValueAt y s z v := ⟨v, hv⟩
  rw [valAt, dif_pos h]
  exact isValueAt_unique hz h.choose_spec hv

def chartMono (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (a : K → ℤ) : Ω :=
  ∏ k, y ⟨k, c k⟩ ^ a k

def IsUnitOn (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (f u : Ω) : Prop :=
  u ≠ 0 ∧ (∃ n : ℕ, f ^ n * u ∈ chartRing ℤ (segreCoord y) c) ∧
    ∃ n : ℕ, f ^ n * u⁻¹ ∈ chartRing ℤ (segreCoord y) c

theorem isUnitOn_one (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (f : Ω) : IsUnitOn y c f 1 :=
  ⟨one_ne_zero, ⟨0, by simpa using one_mem _⟩, ⟨0, by simpa using one_mem _⟩⟩

end Values

section Orbits

def torusSetoid : Setoid ((Σ k, ι k) → ℂ) where
  r z z' := ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z' = torusSmul c z
  iseqv := by
    refine ⟨fun z => ⟨1, fun _ => one_ne_zero, by funext p; simp [torusSmul]⟩, ?_, ?_⟩
    · rintro z z' ⟨c, hc, rfl⟩
      refine ⟨c⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
      funext p
      simp [torusSmul, inv_mul_cancel_left₀ (hc p.1)]
    · rintro z z' z'' ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
      refine ⟨d * c, fun k => mul_ne_zero (hd k) (hc k), ?_⟩
      funext p
      simp [torusSmul, mul_assoc]

def orbitRep (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  Quotient.out (Quotient.mk (torusSetoid (ι := ι)) z)

theorem orbitRep_smul (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    orbitRep (torusSmul c z) = orbitRep z := by
  unfold orbitRep
  congr 1
  exact Quotient.sound ⟨c⁻¹, fun k => inv_ne_zero (hc k), by
    funext p; simp [torusSmul, inv_mul_cancel_left₀ (hc p.1)]⟩

theorem exists_eq_smul_orbitRep (z : (Σ k, ι k) → ℂ) :
    ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c (orbitRep z) :=
  Quotient.mk_out (s := torusSetoid (ι := ι)) z

end Orbits

section Lines

def refNorm (a : K → ℤ) (z : (Σ k, ι k) → ℂ) : ℝ :=
  ∏ k, (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ ((a k : ℝ) / 2)

theorem sq_rpow_half {x : ℝ} (hx : 0 ≤ x) (a : ℤ) : (x ^ 2) ^ ((a : ℝ) / 2) = x ^ a := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx,
    show ((2 : ℕ) : ℝ) * ((a : ℝ) / 2) = ((a : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]

theorem refNorm_smul (a : K → ℤ) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    refNorm a (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * refNorm a z := by
  unfold refNorm
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have : (∑ i, ‖torusSmul c z ⟨k, i⟩‖ ^ 2) = ‖c k‖ ^ 2 * ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [torusSmul, norm_mul, mul_pow]
  rw [this, Real.mul_rpow (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    sq_rpow_half (norm_nonneg _)]

theorem refNorm_pos (a : K → ℤ) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    0 < refNorm a z := by
  refine Finset.prod_pos fun k _ => Real.rpow_pos_of_pos ?_ _
  obtain ⟨i, hi⟩ := hz k
  exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun i _ => sq_nonneg ‖z ⟨k, i⟩‖)
    (Finset.mem_univ i))

variable (ι) in

def hermOfFun (a : K → ℤ) (F : ((Σ k, ι k) → ℂ) → ℝ) : HermLine ι where
  a := a
  h z := refNorm a z * Real.exp (Real.log (F (orbitRep z) / refNorm a (orbitRep z)))
  pos z hz := mul_pos (refNorm_pos a hz) (Real.exp_pos _)
  smul c z hc := by
    change refNorm a (torusSmul c z) * Real.exp (Real.log (F (orbitRep (torusSmul c z)) /
      refNorm a (orbitRep (torusSmul c z)))) = _
    rw [refNorm_smul, orbitRep_smul c hc, mul_assoc]

def IsHomogOfDeg (a : K → ℤ) (F : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z

theorem prod_norm_zpow_pos {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (a : K → ℤ) : 0 < ∏ k, ‖c k‖ ^ a k :=
  Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hc k)) _

theorem hermOfFun_h {a : K → ℤ} {F : ((Σ k, ι k) → ℂ) → ℝ} (hF : IsHomogOfDeg a F)
    {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (hpos : 0 < F z) :
    (hermOfFun ι a F).h z = F z := by
  obtain ⟨c, hc, hzc⟩ := exists_eq_smul_orbitRep z
  set w := orbitRep z with hw
  have hP := prod_norm_zpow_pos hc a
  have hFz : F z = (∏ k, ‖c k‖ ^ a k) * F w := by rw [hzc]; exact hF c w hc
  have hRz : refNorm a z = (∏ k, ‖c k‖ ^ a k) * refNorm a w := by rw [hzc]; exact refNorm_smul a c w
  have hwz : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hz k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [hzc]
    simp [torusSmul, h0]
  have hFw : 0 < F w := by
    rw [hFz] at hpos
    exact pos_of_mul_pos_right hpos hP.le
  have hRw := refNorm_pos a hwz
  show refNorm a z * Real.exp (Real.log (F w / refNorm a w)) = F z
  rw [Real.exp_log (div_pos hFw hRw), hRz, hFz]
  field_simp

end Lines

end GroundTheory.Heights₂.Heights.LowerBoundFree
