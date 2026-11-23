import Mathlib

open Complex Filter Topology Set

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

def dslopeIter (p : ℂ) (k : ℕ) (g : ℂ → ℂ) : ℂ → ℂ :=
  (Function.swap dslope p)^[k] g

lemma dslopeIter_zero (p : ℂ) (g : ℂ → ℂ) : dslopeIter p 0 g = g := rfl

lemma dslopeIter_succ (p : ℂ) (k : ℕ) (g : ℂ → ℂ) :
    dslopeIter p (k + 1) g = dslopeIter p k (Function.swap dslope p g) :=
  Function.iterate_succ_apply _ _ _

lemma dslopeIter_succ' (p : ℂ) (k : ℕ) (g : ℂ → ℂ) :
    dslopeIter p (k + 1) g = Function.swap dslope p (dslopeIter p k g) :=
  Function.iterate_succ_apply' _ _ _

lemma eq_sum_add_dslopeIter (p : ℂ) (g : ℂ → ℂ) (k : ℕ) (z : ℂ) :
    g z = ∑ j ∈ Finset.range k, (z - p) ^ j * dslopeIter p j g p +
      (z - p) ^ k * dslopeIter p k g z := by
  induction k with
  | zero => simp [dslopeIter_zero]
  | succ k ih =>
    rw [ih, Finset.sum_range_succ, dslopeIter_succ']
    have h := sub_smul_dslope (dslopeIter p k g) p z
    simp only [smul_eq_mul] at h
    show _ = _ + _ + (z - p) ^ (k + 1) * dslope (dslopeIter p k g) p z
    rw [pow_succ]
    linear_combination -((z - p) ^ k) * h

lemma analyticAt_dslopeIter {p : ℂ} {g : ℂ → ℂ} (hg : AnalyticAt ℂ g p) (k : ℕ) :
    AnalyticAt ℂ (dslopeIter p k g) p := by
  induction k with
  | zero => exact hg
  | succ k ih =>
    rw [dslopeIter_succ']
    obtain ⟨q, hq⟩ := ih
    exact hq.has_fpower_series_dslope_fslope.analyticAt

lemma swap_dslope_sub_mul {p : ℂ} {g : ℂ → ℂ} (hg : DifferentiableAt ℂ g p) :
    Function.swap dslope p (fun z ↦ (z - p) * g z) = g := by
  funext z
  show dslope (fun z ↦ (z - p) * g z) p z = g z
  rcases eq_or_ne z p with rfl | hz
  · rw [dslope_same]
    exact (((hasDerivAt_id z).sub_const z).mul hg.hasDerivAt).deriv.trans (by simp)
  · rw [dslope_of_ne _ hz, slope_def_field]
    have : z - p ≠ 0 := sub_ne_zero.2 hz
    simp only [sub_self, zero_mul, sub_zero]
    field_simp

lemma swap_dslope_const_mul (p a : ℂ) (g : ℂ → ℂ) :
    Function.swap dslope p (fun z ↦ a * g z) = fun z ↦ a * Function.swap dslope p g z := by
  funext z
  show dslope (fun z ↦ a * g z) p z = a * dslope g p z
  rcases eq_or_ne z p with rfl | hz
  · simp only [dslope_same]
    exact deriv_const_mul_field a
  · simp only [dslope_of_ne _ hz, slope_def_field]
    ring

lemma dslopeIter_const_mul (p a : ℂ) (g : ℂ → ℂ) (k : ℕ) :
    dslopeIter p k (fun z ↦ a * g z) = fun z ↦ a * dslopeIter p k g z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [dslopeIter_succ', ih, swap_dslope_const_mul, dslopeIter_succ']

lemma dslopeIter_congr {p : ℂ} {g₁ g₂ : ℂ → ℂ} (h : g₁ =ᶠ[𝓝 p] g₂) (k : ℕ) :
    dslopeIter p k g₁ =ᶠ[𝓝 p] dslopeIter p k g₂ := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [dslopeIter_succ', dslopeIter_succ']
    have hp : dslopeIter p k g₁ p = dslopeIter p k g₂ p := ih.eq_of_nhds
    filter_upwards [ih] with z hz
    show dslope (dslopeIter p k g₁) p z = dslope (dslopeIter p k g₂) p z
    rcases eq_or_ne z p with rfl | hzp
    · rw [dslope_same, dslope_same, ih.deriv_eq]
    · rw [dslope_of_ne _ hzp, dslope_of_ne _ hzp, slope_def_field, slope_def_field, hz, hp]

open Classical in

def meromorphicShift (f : ℂ → ℂ) (p : ℂ) : ℕ :=
  if h : MeromorphicAt f p then Nat.find h else 0

lemma analyticAt_pow_meromorphicShift_mul {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p) :
    AnalyticAt ℂ (fun z ↦ (z - p) ^ meromorphicShift f p * f z) p := by
  classical
  have := Nat.find_spec hf
  simp only [smul_eq_mul] at this
  unfold meromorphicShift
  rw [dif_pos hf]
  convert this

lemma meromorphicShift_le {f : ℂ → ℂ} {p : ℂ} {n : ℕ}
    (h : AnalyticAt ℂ (fun z ↦ (z - p) ^ n * f z) p) : meromorphicShift f p ≤ n := by
  classical
  have hf : MeromorphicAt f p := ⟨n, by simpa [smul_eq_mul] using h⟩
  unfold meromorphicShift
  rw [dif_pos hf]
  convert Nat.find_min' hf (by simpa [smul_eq_mul] using h)

lemma analyticAt_pow_mul_of_meromorphicShift_le {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p)
    {n : ℕ} (hn : meromorphicShift f p ≤ n) : AnalyticAt ℂ (fun z ↦ (z - p) ^ n * f z) p := by
  induction n, hn using Nat.le_induction with
  | base => exact analyticAt_pow_meromorphicShift_mul hf
  | succ n _ ih =>
    have e : (fun z ↦ (z - p) ^ (n + 1) * f z) = fun z ↦ (z - p) * ((z - p) ^ n * f z) := by
      funext z; ring
    rw [e]
    exact (analyticAt_id.sub analyticAt_const).mul ih

def laurentNumerator (f : ℂ → ℂ) (p : ℂ) : ℂ → ℂ :=
  fun z ↦ (z - p) ^ (meromorphicShift f p + 1) * f z

lemma analyticAt_laurentNumerator {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p) :
    AnalyticAt ℂ (laurentNumerator f p) p :=
  analyticAt_pow_mul_of_meromorphicShift_le hf (Nat.le_succ _)

def laurentCoeff (f : ℂ → ℂ) (p : ℂ) (j : ℕ) : ℂ :=
  dslopeIter p j (laurentNumerator f p) p

def residue (f : ℂ → ℂ) (p : ℂ) : ℂ :=
  laurentCoeff f p (meromorphicShift f p)

def principalPart (f : ℂ → ℂ) (p : ℂ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (meromorphicShift f p + 1),
    laurentCoeff f p j * ((z - p) ^ (meromorphicShift f p + 1 - j))⁻¹

def regularPart (f : ℂ → ℂ) (p : ℂ) : ℂ → ℂ :=
  dslopeIter p (meromorphicShift f p + 1) (laurentNumerator f p)

lemma analyticAt_regularPart {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p) :
    AnalyticAt ℂ (regularPart f p) p :=
  analyticAt_dslopeIter (analyticAt_laurentNumerator hf) _

theorem eq_principalPart_add_regularPart (f : ℂ → ℂ) (p : ℂ) {z : ℂ} (hz : z ≠ p) :
    f z = principalPart f p z + regularPart f p z := by
  set n := meromorphicShift f p
  have h := eq_sum_add_dslopeIter p (laurentNumerator f p) (n + 1) z
  have hzp : z - p ≠ 0 := sub_ne_zero.2 hz
  have hpow : (z - p) ^ (n + 1) ≠ 0 := pow_ne_zero _ hzp
  apply mul_left_cancel₀ hpow
  have e1 : (z - p) ^ (n + 1) * f z = laurentNumerator f p z := rfl
  rw [e1, h, mul_add, principalPart, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ n + 1 := by simp only [Finset.mem_range] at hj; omega
  have e2 : (z - p) ^ (n + 1) = (z - p) ^ (n + 1 - j) * (z - p) ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hj']
  have hpj : (z - p) ^ (n + 1 - j) ≠ 0 := pow_ne_zero _ hzp
  rw [laurentCoeff, e2]
  field_simp
  rfl

theorem residue_eq_dslopeIter {f : ℂ → ℂ} {p : ℂ} {n : ℕ}
    (hn : AnalyticAt ℂ (fun z ↦ (z - p) ^ (n + 1) * f z) p) :
    residue f p = dslopeIter p n (fun z ↦ (z - p) ^ (n + 1) * f z) p := by
  have hf : MeromorphicAt f p := ⟨n + 1, by simpa [smul_eq_mul] using hn⟩
  set m := meromorphicShift f p with hm
  have step : ∀ j, m ≤ j + 1 →
      dslopeIter p (j + 1) (fun z ↦ (z - p) ^ (j + 1 + 1) * f z) p =
        dslopeIter p j (fun z ↦ (z - p) ^ (j + 1) * f z) p := by
    intro j hj
    have hd : DifferentiableAt ℂ (fun z ↦ (z - p) ^ (j + 1) * f z) p :=
      (analyticAt_pow_mul_of_meromorphicShift_le hf hj).differentiableAt
    rw [dslopeIter_succ]
    have e : (fun z ↦ (z - p) ^ (j + 1 + 1) * f z) =
        fun z ↦ (z - p) * ((z - p) ^ (j + 1) * f z) := by
      funext z; ring
    rw [e, swap_dslope_sub_mul hd]
  have up : ∀ j, m ≤ j →
      dslopeIter p j (fun z ↦ (z - p) ^ (j + 1) * f z) p = residue f p := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => rfl
    | succ j hj ih => rw [step j (by omega), ih]
  have hmn : m ≤ n + 1 := meromorphicShift_le hn
  rcases Nat.lt_or_ge n m with h | h
  · rw [← step n (by omega), up (n + 1) (by omega)]
  · exact (up n h).symm

theorem residue_congr {f₁ f₂ : ℂ → ℂ} {p : ℂ} (hf₁ : MeromorphicAt f₁ p)
    (h : f₁ =ᶠ[𝓝[≠] p] f₂) : residue f₁ p = residue f₂ p := by
  set n := meromorphicShift f₁ p + 1
  have h₁ : AnalyticAt ℂ (fun z ↦ (z - p) ^ (n + 1) * f₁ z) p :=
    analyticAt_pow_mul_of_meromorphicShift_le hf₁ (by omega)
  have heq : (fun z ↦ (z - p) ^ (n + 1) * f₁ z) =ᶠ[𝓝 p] fun z ↦ (z - p) ^ (n + 1) * f₂ z := by
    rw [EventuallyEq, eventually_nhdsWithin_iff] at h
    filter_upwards [h] with z hz
    rcases eq_or_ne z p with rfl | hzp
    · simp
    · rw [hz hzp]
  rw [residue_eq_dslopeIter h₁, residue_eq_dslopeIter (h₁.congr heq)]
  exact (dslopeIter_congr heq n).eq_of_nhds

theorem residue_eq_of_eventuallyEq {f u : ℂ → ℂ} {p c : ℂ} (hu : AnalyticAt ℂ u p)
    (h : f =ᶠ[𝓝[≠] p] fun z ↦ c * (z - p)⁻¹ + u z) : residue f p = c := by
  have hG : AnalyticAt ℂ (fun z ↦ c * (z - p) + (z - p) ^ 2 * u z) p := by fun_prop
  have heq : (fun z ↦ (z - p) ^ (1 + 1) * f z) =ᶠ[𝓝 p]
      fun z ↦ c * (z - p) + (z - p) ^ 2 * u z := by
    rw [EventuallyEq, eventually_nhdsWithin_iff] at h
    filter_upwards [h] with z hz
    rcases eq_or_ne z p with rfl | hzp
    · simp
    · rw [hz hzp]
      have : z - p ≠ 0 := sub_ne_zero.2 hzp
      field_simp
  rw [residue_eq_dslopeIter (n := 1) (hG.congr heq.symm), dslopeIter_succ, dslopeIter_zero]
  show dslope _ p p = c
  rw [dslope_same, heq.deriv_eq]
  have hd := (((hasDerivAt_id p).sub_const p).const_mul c).add
    ((((hasDerivAt_id p).sub_const p).pow 2).mul hu.differentiableAt.hasDerivAt)
  exact hd.deriv.trans (by simp)

theorem residue_eq_zero_of_analyticAt {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) :
    residue f p = 0 :=
  residue_eq_of_eventuallyEq hf (Eventually.of_forall fun z ↦ by simp)

lemma swap_dslope_comp_mul {G : ℂ → ℂ} {c w₀ : ℂ} (hc : c ≠ 0)
    (hG : DifferentiableAt ℂ G (c * w₀)) :
    Function.swap dslope w₀ (fun w ↦ G (c * w)) =
      fun w ↦ c * Function.swap dslope (c * w₀) G (c * w) := by
  funext w
  show dslope (fun w ↦ G (c * w)) w₀ w = c * dslope G (c * w₀) (c * w)
  rcases eq_or_ne w w₀ with rfl | hw
  · rw [dslope_same, dslope_same]
    have := hG.hasDerivAt.comp w ((hasDerivAt_id w).const_mul c)
    exact this.deriv.trans (by ring)
  · have hcw : c * w ≠ c * w₀ := fun h ↦ hw (mul_left_cancel₀ hc h)
    have h1 : w - w₀ ≠ 0 := sub_ne_zero.2 hw
    have h2 : c * w - c * w₀ ≠ 0 := sub_ne_zero.2 hcw
    rw [dslope_of_ne _ hw, dslope_of_ne _ hcw, slope_def_field, slope_def_field]
    rw [show c * w - c * w₀ = c * (w - w₀) by ring]
    field_simp

lemma dslopeIter_comp_mul {G : ℂ → ℂ} {c w₀ : ℂ} (hc : c ≠ 0) (hG : AnalyticAt ℂ G (c * w₀))
    (k : ℕ) :
    dslopeIter w₀ k (fun w ↦ G (c * w)) = fun w ↦ c ^ k * dslopeIter (c * w₀) k G (c * w) := by
  induction k with
  | zero => funext w; simp [dslopeIter_zero]
  | succ k ih =>
    rw [dslopeIter_succ', ih]
    rw [swap_dslope_const_mul w₀ (c ^ k) (fun w ↦ dslopeIter (c * w₀) k G (c * w))]
    rw [swap_dslope_comp_mul hc ((analyticAt_dslopeIter hG k).differentiableAt)]
    funext w
    rw [dslopeIter_succ']
    ring

theorem residue_comp_mul {f : ℂ → ℂ} {c w₀ : ℂ} (hc : c ≠ 0) (hf : MeromorphicAt f (c * w₀)) :
    residue (fun w ↦ f (c * w)) w₀ = c⁻¹ * residue f (c * w₀) := by
  set n := meromorphicShift f (c * w₀)
  set G : ℂ → ℂ := fun z ↦ (z - c * w₀) ^ (n + 1) * f z with hGdef
  have hG : AnalyticAt ℂ G (c * w₀) := analyticAt_pow_mul_of_meromorphicShift_le hf (Nat.le_succ n)
  have e : (fun w ↦ (w - w₀) ^ (n + 1) * f (c * w)) = fun w ↦ c⁻¹ ^ (n + 1) * G (c * w) := by
    funext w
    simp only [hGdef]
    rw [← mul_assoc, ← mul_pow]
    congr 2
    field_simp
  have hcomp : AnalyticAt ℂ (fun w ↦ G (c * w)) w₀ := by
    have : AnalyticAt ℂ (fun w ↦ c * w) w₀ := by fun_prop
    exact hG.comp_of_eq this rfl
  have hana : AnalyticAt ℂ (fun w ↦ (w - w₀) ^ (n + 1) * f (c * w)) w₀ := by
    rw [e]
    exact analyticAt_const.mul hcomp
  rw [residue_eq_dslopeIter hana, e, dslopeIter_const_mul, dslopeIter_comp_mul hc hG]
  have : residue f (c * w₀) = dslopeIter (c * w₀) n G (c * w₀) := rfl
  rw [this, inv_pow, pow_succ]
  field_simp

theorem residue_logDeriv {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p) {n : ℤ}
    (hn : meromorphicOrderAt f p = n) : residue (logDeriv f) p = n := by
  obtain ⟨g, hg, hgp, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hn
  simp only [smul_eq_mul] at hfg
  have hu : AnalyticAt ℂ (fun z ↦ deriv g z / g z) p := hg.deriv.div hg hgp
  apply residue_eq_of_eventuallyEq hu
  have h2 : ∀ᶠ z in 𝓝[≠] p, f =ᶠ[𝓝 z] fun w ↦ (w - p) ^ n * g w := by
    have := eventually_eventually_nhdsWithin.2 hfg
    filter_upwards [this, self_mem_nhdsWithin] with z hz hzp
    rwa [nhdsWithin_eq_nhds.2 (isOpen_compl_singleton.mem_nhds hzp)] at hz
  have h3 : ∀ᶠ z in 𝓝[≠] p, g z ≠ 0 :=
    nhdsWithin_le_nhds (hg.continuousAt.eventually_ne hgp)
  have h4 : ∀ᶠ z in 𝓝[≠] p, AnalyticAt ℂ g z := nhdsWithin_le_nhds hg.eventually_analyticAt
  filter_upwards [h2, h3, h4, self_mem_nhdsWithin] with z hz hgz hga hzp
  have hzp' : z - p ≠ 0 := sub_ne_zero.2 hzp
  have h1 : HasDerivAt (fun w ↦ (w - p) ^ n) ((n : ℂ) * (z - p) ^ (n - 1) * 1) z := by
    have := (hasDerivAt_zpow n (z - p) (Or.inl hzp')).comp z ((hasDerivAt_id z).sub_const p)
    exact this
  have hd : HasDerivAt (fun w ↦ (w - p) ^ n * g w)
      ((n : ℂ) * (z - p) ^ (n - 1) * 1 * g z + (z - p) ^ n * deriv g z) z :=
    h1.mul hga.differentiableAt.hasDerivAt
  rw [logDeriv_apply, hz.deriv_eq, hz.eq_of_nhds, hd.deriv, zpow_sub_one₀ hzp']
  have hzn : (z - p) ^ n ≠ 0 := zpow_ne_zero n hzp'
  field_simp

theorem residue_ne_zero_of_meromorphicOrderAt_eq_neg_one {f : ℂ → ℂ} {p : ℂ}
    (hf : MeromorphicAt f p) (h : meromorphicOrderAt f p = ((-1 : ℤ) : WithTop ℤ)) :
    residue f p ≠ 0 := by
  obtain ⟨g, hg, hgp, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).1 h
  simp only [smul_eq_mul] at hfg
  obtain ⟨q, hq⟩ := hg
  have hu : AnalyticAt ℂ (dslope g p) p := hq.has_fpower_series_dslope_fslope.analyticAt
  rw [residue_eq_of_eventuallyEq (c := g p) hu ?_]
  · exact hgp
  filter_upwards [hfg, self_mem_nhdsWithin] with z hz hzp
  have hzp' : z - p ≠ 0 := sub_ne_zero.2 hzp
  have e := sub_smul_dslope g p z
  simp only [smul_eq_mul] at e
  rw [hz, zpow_neg_one]
  field_simp
  linear_combination -e

end Elliptic
end GroundTheory.Global
