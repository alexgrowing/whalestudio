import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowDomainCriterionHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bExpHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos

namespace GlobalTheory.LaurentFJ

open Complex ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

theorem coeff_eq_zero_of_hasSum_zero (d : ℤ → ℂ)
    (h : ∀ t : ℝ, HasSum (fun k : ℤ => d k * cexp (2 * Real.pi * I * t) ^ k) 0) (j : ℤ) :
    d j = 0 := by
  have hs : Summable fun k => ‖d k‖ := by
    have := (h 0).summable
    simp only [ofReal_zero, mul_zero, Complex.exp_zero, one_zpow, mul_one] at this
    exact summable_norm_iff.mpr this
  have hpow : ∀ (k : ℤ) (t : ℝ), cexp (2 * Real.pi * I * t) ^ k * cexp (2 * Real.pi * I * t) ^ (-j)
      = cexp ((2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t) := by
    intro k t
    rw [← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hI := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := MeasureTheory.volume)
    (a := 0) (b := 1) (f := fun _ : ℝ => (0 : ℂ))
    (F := fun (k : ℤ) (t : ℝ) => d k * cexp ((2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t))
    (fun k _ => ‖d k‖)
    (fun k => (by fun_prop : Continuous fun t : ℝ =>
      d k * cexp ((2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t)).aestronglyMeasurable)
    (fun k => MeasureTheory.ae_of_all _ fun t _ => by
      have : (2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t =
          ((2 * Real.pi * ((k - j : ℤ) : ℝ) * t : ℝ) : ℂ) * I := by push_cast; ring
      rw [norm_mul, this, Complex.norm_exp_ofReal_mul_I, mul_one])
    (MeasureTheory.ae_of_all _ fun t _ => hs) intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun t _ => by
      have := (h t).mul_right (cexp (2 * Real.pi * I * t) ^ (-j))
      simp only [zero_mul, mul_assoc (d _), hpow] at this
      exact this)
  have hval : ∀ k : ℤ, (∫ t in (0 : ℝ)..1,
      d k * cexp ((2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t)) = if k = j then d j else 0 := by
    intro k
    split_ifs with hk
    · subst hk; simp
    · have hc : (2 * Real.pi * I * ((k - j : ℤ) : ℂ)) ≠ 0 := by
        refine mul_ne_zero Complex.two_pi_I_ne_zero ?_
        exact_mod_cast sub_ne_zero.mpr hk
      rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hc]
      have : cexp (2 * Real.pi * I * ((k - j : ℤ) : ℂ)) = 1 := by
        rw [mul_comm]; exact Complex.exp_int_mul_two_pi_mul_I _
      simp only [ofReal_one, mul_one, ofReal_zero, mul_zero, Complex.exp_zero, this]
      simp
  simp only [hval, intervalIntegral.integral_zero] at hI
  exact (hasSum_ite_eq j (d j)).unique hI

theorem hasSum_fiber_of_hasSum_line {ι : Type*} (c : ι → ℂ) (n : ι → ℤ) (a : ℤ → ℂ) (y : ℝ)
    (f : ℝ → ℂ)
    (ha : ∀ t : ℝ, HasSum (fun k : ℤ => a k * cexp (2 * Real.pi * I * (t + y * I)) ^ k) (f t))
    (hc : ∀ t : ℝ, HasSum (fun i => c i * cexp (2 * Real.pi * I * (t + y * I)) ^ n i) (f t))
    (j : ℤ) : HasSum (fun i : {i // n i = j} => c i) (a j) := by
  have hsum : ∀ k : ℤ, Summable fun i : {i // n i = k} => c i := by
    intro k
    have h1 := ((hc 0).summable.subtype fun i => n i = k).mul_right
      (cexp (2 * Real.pi * I * ((0 : ℝ) + y * I)) ^ (-k))
    refine h1.congr fun i => ?_
    have hi : n i = k := i.2
    simp only [Function.comp_apply, hi]
    rw [mul_assoc, ← zpow_add₀ (Complex.exp_ne_zero _)]
    simp
  have hb : ∀ t : ℝ, HasSum (fun k : ℤ => (∑' i : {i // n i = k}, c i) *
      cexp (2 * Real.pi * I * (t + y * I)) ^ k) (f t) := by
    intro t
    have h1 := (Equiv.sigmaFiberEquiv n).hasSum_iff.mpr (hc t)
    refine h1.sigma fun k => ?_
    have := (hsum k).hasSum.mul_right (cexp (2 * Real.pi * I * (t + y * I)) ^ k)
    refine this.congr_fun fun i => ?_
    simp only [Function.comp_apply, Equiv.sigmaFiberEquiv, Equiv.coe_fn_mk, i.2]
  have hz := coeff_eq_zero_of_hasSum_zero
    (fun k => (a k - ∑' i : {i // n i = k}, c i) * cexp (2 * Real.pi * I * (y * I)) ^ k)
    (fun t => by
      have := (ha t).sub (hb t)
      rw [sub_self] at this
      refine this.congr_fun fun k => ?_
      rw [mul_add, Complex.exp_add, mul_zpow]; ring) j
  have hz' : a j = ∑' i : {i // n i = j}, c i :=
    sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (zpow_ne_zero _ (Complex.exp_ne_zero _)))
  rw [hz']
  exact (hsum j).hasSum

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}

theorem flow_mem_dom_of_im_nonneg (X : Data E r) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hs : ∀ τ, 0 ≤ (s τ).im) :
    X.flow ξ s x ∈ X.dom := by
  have hiv : X.IsIsoV fun τ => Data.emb τ.1 ξ := by
    intro τ
    refine ⟨?_, ?_⟩
    · have key : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = τ.1 (herm X.Gm ξ ξ) := by
        simp only [hermC, herm, Data.emb, map_sum, map_mul, cc,
          NumberField.IsCMField.complexEmbedding_complexConj]
      change hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0
      rw [key, hξ.2.1, map_zero]
    · intro h0
      apply hξ.2.2
      funext a
      have := congrFun h0 a
      simpa [Data.emb] using this
  refine (flowDomainCriterion_holds r X _ hiv x hx s).1.2 fun τ => ?_
  have ht : 0 < X.ttV (fun τ => Data.emb τ.1 ξ) x τ :=
    one_div_pos.mpr (mul_pos (MajorantFamilyNorms.c_pos X τ) (X.maj_pos hx τ (hiv τ).2))
  have := div_nonneg (hs τ) ht.le
  linarith

theorem hasSum_fj_of_line (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}
    (hP : X.IsSec la P) {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (sb : X.Ψ → ℝ)
    (hint : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → ∃ k : ℤ, 2 * ∑ τ, ν τ * sb τ = k)
    (κ u₁ : ℂ) (a : ℤ → ℂ) (y : ℝ)
    (hdom : ∀ w : ℂ, w.im = y → X.flow ξ (fun τ => w * sb τ) x ∈ X.dom)
    (ha : ∀ w : ℂ, w.im = y → HasSum (fun n : ℤ => a n * (u₁ * cexp (2 * Real.pi * I * w)) ^ n)
      (κ * P (X.flow ξ (fun τ => w * sb τ) x))) (j : ℤ) :
    HasSum (fun ν : {ν : X.Ψ → ℝ // 2 * ∑ τ, ν τ * sb τ = j} => κ * X.fj la ξ ν P x)
      (a j * u₁ ^ j) := by
  classical
  set n : (X.Ψ → ℝ) → ℤ := fun ν => ⌊2 * ∑ τ, ν τ * sb τ⌋ with hn
  have hnν : ∀ ν, X.fj la ξ ν P x ≠ 0 → 2 * ∑ τ, ν τ * sb τ = n ν := by
    intro ν hν
    obtain ⟨k, hk⟩ := hint ν hν
    simp only [hn, hk, Int.floor_intCast]
  have him : ∀ t : ℝ, ((t : ℂ) + y * I).im = y := fun t => by simp
  have H := hasSum_fiber_of_hasSum_line (fun ν => κ * X.fj la ξ ν P x) n
    (fun k => a k * u₁ ^ k) y (fun t => κ * P (X.flow ξ (fun τ => ((t : ℂ) + y * I) * sb τ) x))
    (fun t => by
      convert ha _ (him t) using 2 with k
      rw [mul_zpow, mul_assoc])
    (fun t => by
      have := (m3bExp_holds r X la P hP ξ hξ x hx _ (hdom _ (him t))).mul_left κ
      refine this.congr_fun fun ν => ?_
      rw [mul_assoc]
      by_cases hν : X.fj la ξ ν P x = 0
      · simp [hν]
      · congr 2
        rw [← Complex.exp_int_mul]
        congr 1
        have h2 : ((n ν : ℤ) : ℂ) = 2 * ∑ τ, (ν τ : ℂ) * sb τ := by
          have := congrArg (fun z : ℝ => (z : ℂ)) (hnν ν hν)
          push_cast at this
          exact this.symm
        have h3 : ∑ τ, (ν τ : ℂ) * (((t : ℂ) + y * I) * sb τ) =
            ((t : ℂ) + y * I) * ∑ τ, (ν τ : ℂ) * sb τ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => by ring
        rw [h2, h3]; ring) j
  have e1 := (hasSum_subtype_iff_indicator (s := {ν | n ν = j})
    (f := fun ν => κ * X.fj la ξ ν P x)).mp H
  refine (hasSum_subtype_iff_indicator (s := {ν : X.Ψ → ℝ | 2 * ∑ τ, ν τ * sb τ = j})
    (f := fun ν => κ * X.fj la ξ ν P x)).mpr ?_
  convert e1 using 1
  funext ν
  by_cases hν : X.fj la ξ ν P x = 0
  · simp [Set.indicator_apply, hν]
  · have : (2 * ∑ τ, ν τ * sb τ = j) ↔ n ν = j := by
      rw [hnν ν hν]; exact Int.cast_inj
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, this]

theorem hasSum_fj (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}
    (hP : X.IsSec la P) {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (sb : X.Ψ → ℝ) (hsb : ∀ τ, 0 ≤ sb τ)
    (hint : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → ∃ k : ℤ, 2 * ∑ τ, ν τ * sb τ = k)
    (κ u₁ : ℂ) (a : ℤ → ℂ) (T : ℝ)
    (ha : ∀ w : ℂ, T < w.im → HasSum (fun n : ℤ => a n * (u₁ * cexp (2 * Real.pi * I * w)) ^ n)
      (κ * P (X.flow ξ (fun τ => w * sb τ) x))) (j : ℤ) :
    HasSum (fun ν : {ν : X.Ψ → ℝ // 2 * ∑ τ, ν τ * sb τ = j} => κ * X.fj la ξ ν P x)
      (a j * u₁ ^ j) := by
  refine hasSum_fj_of_line X hP hξ hx sb hint κ u₁ a (max T 0 + 1) (fun w hw => ?_)
    (fun w hw => ha w (by rw [hw]; linarith [le_max_left T 0])) j
  refine flow_mem_dom_of_im_nonneg X hξ hx _ fun τ => ?_
  simp only [mul_im, ofReal_re, ofReal_im, mul_zero, zero_add, hw]
  exact mul_nonneg (by linarith [le_max_right T 0]) (hsb τ)

theorem coeff_mul_zpow_eq_mul_fj (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}
    (hP : X.IsSec la P) {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (sb : X.Ψ → ℝ) (hsb : ∀ τ, 0 ≤ sb τ) (ν₀ : X.Ψ → ℝ) (j : ℤ)
    (hj : 2 * ∑ τ, ν₀ τ * sb τ = j)
    (huniq : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → 2 * ∑ τ, ν τ * sb τ = j → ν = ν₀)
    (hint : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → ∃ k : ℤ, 2 * ∑ τ, ν τ * sb τ = k)
    (κ u₁ : ℂ) (a : ℤ → ℂ) (T : ℝ)
    (ha : ∀ w : ℂ, T < w.im → HasSum (fun n : ℤ => a n * (u₁ * cexp (2 * Real.pi * I * w)) ^ n)
      (κ * P (X.flow ξ (fun τ => w * sb τ) x))) :
    a j * u₁ ^ j = κ * X.fj la ξ ν₀ P x := by
  refine (hasSum_fj X hP hξ hx sb hsb hint κ u₁ a T ha j).unique ?_
  refine hasSum_single (f := fun ν : {ν : X.Ψ → ℝ // 2 * ∑ τ, ν τ * sb τ = j} =>
    κ * X.fj la ξ ν P x) ⟨ν₀, hj⟩ fun ν hν => ?_
  by_cases h0 : X.fj la ξ ν P x = 0
  · simp [h0]
  · exact absurd (Subtype.ext (huniq ν h0 ν.2)) hν

theorem coeff_eq_fj (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}
    (hP : X.IsSec la P) {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (sb : X.Ψ → ℝ) (hsb : ∀ τ, 0 < sb τ) (ν₀ : X.Ψ → ℝ) (j : ℤ)
    (hj : 2 * ∑ τ, ν₀ τ * sb τ = j)
    (huniq : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → 2 * ∑ τ, ν τ * sb τ = j → ν = ν₀)
    (hint : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → ∃ k : ℤ, 2 * ∑ τ, ν τ * sb τ = k)
    (a : ℤ → ℂ) (T : ℝ)
    (ha : ∀ w : ℂ, T < w.im → HasSum (fun n : ℤ => a n * cexp (2 * Real.pi * I * w) ^ n)
      (P (X.flow ξ (fun τ => w * sb τ) x))) :
    a j = X.fj la ξ ν₀ P x := by
  simpa using coeff_mul_zpow_eq_mul_fj X hP hξ hx sb (fun τ => (hsb τ).le) ν₀ j hj huniq hint
    1 1 a T (by simpa using ha)

theorem coeff_eq_zero_of_mem_SSgt' (X : Data E r) {la : Wt X.Ψ r} {c : ℝ} {P : Frame X.Ψ r → ℂ}
    (hP : P ∈ X.SSgt la c) {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (sb : X.Ψ → ℝ) (hsb : ∀ τ, 0 ≤ sb τ) (ν₀ : X.Ψ → ℝ) (hν₀ : ∑ τ, ν₀ τ ≤ c) (j : ℤ)
    (hj : 2 * ∑ τ, ν₀ τ * sb τ = j)
    (huniq : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → 2 * ∑ τ, ν τ * sb τ = j → ν = ν₀)
    (hint : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → ∃ k : ℤ, 2 * ∑ τ, ν τ * sb τ = k)
    (κ u₁ : ℂ) (hu₁ : u₁ ≠ 0) (a : ℤ → ℂ) (T : ℝ)
    (ha : ∀ w : ℂ, T < w.im → HasSum (fun n : ℤ => a n * (u₁ * cexp (2 * Real.pi * I * w)) ^ n)
      (κ * P (X.flow ξ (fun τ => w * sb τ) x))) :
    a j = 0 := by
  have h := coeff_mul_zpow_eq_mul_fj X hP.1.1.1 hξ hx sb hsb ν₀ j hj huniq hint κ u₁ a T ha
  rw [hP.2 ξ hξ ν₀ hν₀ x hx, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_right (zpow_ne_zero _ hu₁)

theorem coeff_eq_zero_of_mem_SSgt (X : Data E r) {la : Wt X.Ψ r} {c : ℝ} {P : Frame X.Ψ r → ℂ}
    (hP : P ∈ X.SSgt la c) {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (sb : X.Ψ → ℝ) (hsb : ∀ τ, 0 < sb τ) (ν₀ : X.Ψ → ℝ) (hν₀ : ∑ τ, ν₀ τ ≤ c) (j : ℤ)
    (hj : 2 * ∑ τ, ν₀ τ * sb τ = j)
    (huniq : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → 2 * ∑ τ, ν τ * sb τ = j → ν = ν₀)
    (hint : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → ∃ k : ℤ, 2 * ∑ τ, ν τ * sb τ = k)
    (a : ℤ → ℂ) (T : ℝ)
    (ha : ∀ w : ℂ, T < w.im → HasSum (fun n : ℤ => a n * cexp (2 * Real.pi * I * w) ^ n)
      (P (X.flow ξ (fun τ => w * sb τ) x))) :
    a j = 0 := by
  rw [coeff_eq_fj X hP.1.1.1 hξ hx sb hsb ν₀ j hj huniq hint a T ha, hP.2 ξ hξ ν₀ hν₀ x hx]

end

end GlobalTheory.LaurentFJ
