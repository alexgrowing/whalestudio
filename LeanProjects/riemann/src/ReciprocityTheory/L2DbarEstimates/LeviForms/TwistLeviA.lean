import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.CommFderivApply
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ExistsChartPartition

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

noncomputable section

def tlFlr (a b s : ℝ) : ℝ := s + Real.smoothTransition ((a - s) / (a - b)) * (a - s)

theorem tlFlr_contDiff (a b : ℝ) : ContDiff ℝ ∞ (tlFlr a b) := by
  unfold tlFlr
  fun_prop

theorem tlFlr_eq (a b s : ℝ) (hab : b < a) (h : a ≤ s) : tlFlr a b s = s := by
  unfold tlFlr
  have h1 : (a - s) / (a - b) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  rw [Real.smoothTransition.zero_of_nonpos h1]; ring

theorem tlFlr_ge (a b s : ℝ) (hab : b < a) : b ≤ tlFlr a b s := by
  unfold tlFlr
  have hT0 := Real.smoothTransition.nonneg ((a - s) / (a - b))
  rcases le_total a s with h | h
  · nlinarith [Real.smoothTransition.le_one ((a - s) / (a - b))]
  · rcases le_total s b with h' | h'
    · have : 1 ≤ (a - s) / (a - b) := by rw [le_div_iff₀ (by linarith)]; linarith
      rw [Real.smoothTransition.one_of_one_le this]; linarith
    · nlinarith

theorem tl_eta_pos (s : ℝ) (hs : 9 / 10 ≤ s) : 0 < s + Real.log s := by
  have h := Real.one_sub_inv_le_log_of_pos (show 0 < s by linarith)
  have : 0 < s + 1 - s⁻¹ := by
    have hs0 : 0 < s := by linarith
    have : s⁻¹ ≤ 10 / 9 := by rw [inv_le_comm₀ hs0 (by norm_num)]; linarith
    linarith
  linarith

def tlK (c t : ℝ) : ℝ :=
  -Real.log (tlFlr (19 / 20) (9 / 10) (c - t) + Real.log (tlFlr (19 / 20) (9 / 10) (c - t)))

theorem tlK_contDiff (c : ℝ) : ContDiff ℝ ∞ (tlK c) := by
  have hf : ContDiff ℝ ∞ (fun t => tlFlr (19 / 20) (9 / 10) (c - t)) :=
    (tlFlr_contDiff _ _).comp (contDiff_const.sub contDiff_id)
  have hge : ∀ t, 9 / 10 ≤ tlFlr (19 / 20) (9 / 10) (c - t) := fun t => tlFlr_ge _ _ _ (by norm_num)
  have hl : ContDiff ℝ ∞ (fun t => Real.log (tlFlr (19 / 20) (9 / 10) (c - t))) :=
    hf.log fun t => by linarith [hge t]
  have hs : ContDiff ℝ ∞ (fun t => tlFlr (19 / 20) (9 / 10) (c - t) + Real.log (tlFlr (19 / 20) (9 / 10) (c - t))) :=
    hf.add hl
  exact (hs.log fun t => (tl_eta_pos _ (hge t)).ne').neg

open Filter Topology

def tlKp (c t : ℝ) : ℝ := (1 + 1 / (c - t)) / ((c - t) + Real.log (c - t))

def tlKpp (c t : ℝ) : ℝ :=
  1 / ((c - t) ^ 2 * ((c - t) + Real.log (c - t))) + ((1 + 1 / (c - t)) / ((c - t) + Real.log (c - t))) ^ 2

theorem tlK_eventually (c t : ℝ) (ht : t < c - 19 / 20) :
    tlK c =ᶠ[𝓝 t] fun t => -Real.log ((c - t) + Real.log (c - t)) := by
  filter_upwards [Iio_mem_nhds ht] with y hy
  have : tlFlr (19 / 20) (9 / 10) (c - y) = c - y := tlFlr_eq _ _ _ (by norm_num) (by simp at hy; linarith)
  simp only [tlK, this]

theorem tl_hasDerivAt_k (c t : ℝ) (hs : 9 / 10 ≤ c - t) :
    HasDerivAt (fun t => -Real.log ((c - t) + Real.log (c - t))) (tlKp c t) t := by
  have hs0 : c - t ≠ 0 := by intro h; linarith
  have he := tl_eta_pos _ hs
  have hu : HasDerivAt (fun y => c - y) (-1) t := by simpa using (hasDerivAt_id t).const_sub c
  have hl := hu.log hs0
  have h2 := (hu.add hl).log he.ne'
  refine h2.neg.congr_deriv ?_
  unfold tlKp
  simp only [Pi.add_apply, Pi.div_apply]
  field_simp
  ring

theorem tl_hasDerivAt_kp (c t : ℝ) (hs : 9 / 10 ≤ c - t) : HasDerivAt (tlKp c) (tlKpp c t) t := by
  have hs0 : c - t ≠ 0 := by intro h; linarith
  have he := tl_eta_pos _ hs
  have hu : HasDerivAt (fun y => c - y) (-1) t := by simpa using (hasDerivAt_id t).const_sub c
  have hi := (hasDerivAt_const t (1 : ℝ)).div hu hs0
  have hk := (hasDerivAt_const t (1 : ℝ)).add hi
  have hl := hu.log hs0
  have h2 := hk.div (hu.add hl) he.ne'
  refine h2.congr_deriv ?_
  unfold tlKpp
  simp only [Pi.add_apply, Pi.div_apply]
  field_simp
  ring

theorem tl_deriv_k (c t : ℝ) (ht : t ≤ c - 1) :
    deriv (tlK c) t = tlKp c t ∧ deriv (deriv (tlK c)) t = tlKpp c t := by
  have ht' : t < c - 19 / 20 := by linarith
  have hE : deriv (tlK c) =ᶠ[𝓝 t] tlKp c := by
    filter_upwards [Iio_mem_nhds ht'] with y hy
    simp only [Set.mem_Iio] at hy
    exact ((tl_hasDerivAt_k c y (by linarith)).congr_of_eventuallyEq (tlK_eventually c y hy)).deriv
  refine ⟨hE.eq_of_nhds, ?_⟩
  exact ((tl_hasDerivAt_kp c t (by linarith)).congr_of_eventuallyEq hE).deriv

theorem tl_ev_nonneg {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (x : M) :
    0 ≤ ev n g ph r x := by
  unfold ev; positivity

theorem tl_ev_le_one {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (hr : 0 < r)
    (hbd : ∀ x, (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) ≤ r ^ 2) (x : M) :
    ev n g ph r x ≤ 1 := by
  unfold ev
  rw [div_le_one (by positivity)]
  exact hbd x

theorem tl_lw_le {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r ε : ℝ) (hr : 0 < r)
    (hε : 0 < ε) (hbd : ∀ x, (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) ≤ r ^ 2) (x : M) :
    lw n g ph r ε x ≤ Real.log (1 + ε ^ 2) := by
  unfold lw
  have h0 := tl_ev_nonneg n g ph r x
  have h1 := tl_ev_le_one n g ph r hr hbd x
  exact Real.log_le_log (by positivity) (by linarith)

theorem tl_ev_smoothR {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : Fin n → M → ℂ)
    (ph : M → ℝ) (r : ℝ) (hg : ∀ i, Holo n z (g i)) (hph : SmoothR n z ph) :
    SmoothR n z (ev n g ph r) := by
  have hS : SmoothR n z (fun x => ∑ i, ‖g i x‖ ^ 2) :=
    smoothR_sum n z Finset.univ _ fun i _ => Smooth.normSq n z _ (Holo.smooth n z _ (hg i))
  have hE : SmoothR n z (fun x => Real.exp (-ph x)) :=
    SmoothR.comp n z (fun t => Real.exp (-t)) (Real.contDiff_exp.comp contDiff_neg) ph hph
  exact SmoothR.comp n z (fun t => t / r ^ 2) (contDiff_id.div_const _) _ (SmoothR.mul n z _ _ hS hE)

theorem tl_lw_smoothR {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : Fin n → M → ℂ)
    (ph : M → ℝ) (r δ : ℝ) (hg : ∀ i, Holo n z (g i)) (hph : SmoothR n z ph) (hδ : 0 < δ) :
    SmoothR n z (lw n g ph r δ) := by
  have hd : 0 < δ ^ 2 := by positivity
  have hL : ContDiff ℝ ∞ (fun t => Real.log (tlFlr (δ ^ 2) (δ ^ 2 / 2) t)) :=
    (tlFlr_contDiff _ _).log fun t => by
      have := tlFlr_ge (δ ^ 2) (δ ^ 2 / 2) t (by linarith)
      exact (show 0 < tlFlr (δ ^ 2) (δ ^ 2 / 2) t by linarith).ne'
  have h := SmoothR.comp n z _ hL (fun x => ev n g ph r x + δ ^ 2)
    (SmoothR.add n z _ _ (tl_ev_smoothR n z g ph r hg hph) (smoothR_const n z _))
  have heq : (fun x => Real.log (tlFlr (δ ^ 2) (δ ^ 2 / 2) (ev n g ph r x + δ ^ 2))) = lw n g ph r δ := by
    funext x
    unfold lw
    rw [tlFlr_eq _ _ _ (by linarith) (by linarith [tl_ev_nonneg n g ph r x])]
  rw [heq] at h
  exact h

theorem tl_twist_eq {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r ε : ℝ) (hr : 0 < r)
    (hε : 0 < ε) (hbd : ∀ x, (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) ≤ r ^ 2) :
    twist n g ph r ε = fun x => tlK (1 + Real.log (1 + ε ^ 2)) (lw n g ph r ε x) := by
  funext x
  have h := tl_lw_le n g ph r ε hr hε hbd x
  unfold twist eta xx tlK
  rw [tlFlr_eq _ _ _ (by norm_num) (by linarith)]

theorem tl_levi_formula {M : Type*} [TopologicalSpace M] (n : ℕ) (hCh : ChainStatement n M)
    (z : M → V n) (g : Fin n → M → ℂ) (ph ph2 : M → ℝ) (r : ℝ) (j : ℕ) (ε δ : ℝ)
    (hz : IsLocalHomeomorph z) (hg : ∀ i, Holo n z (g i)) (hph : SmoothR n z ph)
    (hph2 : SmoothR n z ph2) (hr : 0 < r) (hε : 0 < ε) (hδ : 0 < δ)
    (hbd : ∀ x, (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) ≤ r ^ 2) (x : M) (ξ : Fin n → ℂ) :
    (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re =
      (Levi n z ph2 x ξ).re + ((n : ℝ) + j) * (Levi n z ph x ξ).re +
        (n : ℝ) * (Levi n z (lw n g ph r δ) x ξ).re +
        tlKp (1 + Real.log (1 + ε ^ 2)) (lw n g ph r ε x) * (Levi n z (lw n g ph r ε) x ξ).re +
        tlKpp (1 + Real.log (1 + ε ^ 2)) (lw n g ph r ε x) *
          ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ ^ 2 := by
  set c := 1 + Real.log (1 + ε ^ 2) with hc
  have hlε := tl_lw_smoothR n z g ph r ε hg hph hε
  have hlδ := tl_lw_smoothR n z g ph r δ hg hph hδ
  have hA : SmoothR n z (fun y => ph2 y + ((n : ℝ) + j) * ph y) :=
    SmoothR.add n z _ _ hph2 (SmoothR.mul n z _ _ (smoothR_const n z _) hph)
  have hBB : SmoothR n z (fun y => (n : ℝ) * lw n g ph r δ y) :=
    SmoothR.mul n z _ _ (smoothR_const n z _) hlδ
  have hwgt : SmoothR n z (wgt n g ph ph2 r j δ) := SmoothR.add n z _ _ hA hBB
  have htw_eq := tl_twist_eq n g ph r ε hr hε hbd
  have htw : SmoothR n z (twist n g ph r ε) := by
    rw [htw_eq]; exact SmoothR.comp n z _ (tlK_contDiff c) _ hlε
  have e1 : Levi n z (wgt n g ph ph2 r j δ) x ξ =
      Levi n z ph2 x ξ + (((n : ℝ) + j : ℝ) : ℂ) * Levi n z ph x ξ +
        ((n : ℝ) : ℂ) * Levi n z (lw n g ph r δ) x ξ := by
    have h1 := levi_add n z _ _ (SmoothR.ckR n z 2 _ hA) (SmoothR.ckR n z 2 _ hBB) x ξ
    have h2 := levi_add n z _ _ (SmoothR.ckR n z 2 _ hph2)
      (SmoothR.ckR n z 2 _ (SmoothR.mul n z _ _ (smoothR_const n z ((n : ℝ) + j)) hph)) x ξ
    have h3 := levi_const_mul n z ((n : ℝ) + j) ph (SmoothR.ckR n z 2 _ hph) x ξ
    have h4 := levi_const_mul n z (n : ℝ) _ (SmoothR.ckR n z 2 _ hlδ) x ξ
    change Levi n z (fun y => ph2 y + ((n : ℝ) + j) * ph y + (n : ℝ) * lw n g ph r δ y) x ξ = _
    rw [h1, h2, h3, h4]
  have hk : ContDiff ℝ 2 (tlK c) := contDiff_infty.1 (tlK_contDiff c) 2
  have e2 : Levi n z (twist n g ph r ε) x ξ =
      ((tlKp c (lw n g ph r ε x) : ℝ) : ℂ) * Levi n z (lw n g ph r ε) x ξ +
        ((tlKpp c (lw n g ph r ε x) : ℝ) : ℂ) *
          ((‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [htw_eq, hCh z hz (tlK c) (lw n g ph r ε) hk hlε x ξ]
    obtain ⟨d1, d2⟩ := tl_deriv_k c (lw n g ph r ε x) (by linarith [tl_lw_le n g ph r ε hr hε hbd x])
    rw [d1, d2]
  rw [levi_add n z _ _ (SmoothR.ckR n z 2 _ hwgt) (SmoothR.ckR n z 2 _ htw) x ξ, e1, e2]
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
  ring

end

end ReciprocityTheory.L2DbarEstimates.I
