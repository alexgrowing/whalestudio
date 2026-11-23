import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SameOrbitRefl
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicConjugatePullbackStatement
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

section Holo

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem pot_holoOn_mono {V W : Set X} {g : X → ℂ} (h : A.HoloOn V g) (hW : W ⊆ V) :
    A.HoloOn W g :=
  fun j w hw => h j w ⟨hw.1, hW hw.2⟩

theorem pot_holoOn_continuousOn {V : Set X} (hV : IsOpen V) {g : X → ℂ} (h : A.HoloOn V g) :
    ContinuousOn g V := by
  intro y hy
  obtain ⟨j, hj⟩ := A.cover y
  have hw : A.chart j y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' V :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hy⟩
  have h1 := (h j _ hw).continuousAt
  have h2 : ContinuousAt (A.chart j) y := (A.chart j).continuousAt hj
  have h3 : ContinuousAt (fun y' => (g ∘ (A.chart j).symm) (A.chart j y')) y :=
    ContinuousAt.comp (g := g ∘ (A.chart j).symm) h1 h2
  refine (h3.congr ?_).continuousWithinAt
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y' hy'
  simp [(A.chart j).left_inv hy']

theorem pot_holoOn_sub_add {V : Set X} {g₁ g₂ g₃ : X → ℂ} (h₁ : A.HoloOn V g₁)
    (h₂ : A.HoloOn V g₂) (h₃ : A.HoloOn V g₃) :
    A.HoloOn V (fun y => g₁ y - g₂ y + g₃ y) :=
  fun j w hw => ((h₁ j w hw).sub (h₂ j w hw)).add (h₃ j w hw)

theorem pot_holoOn_div {V : Set X} {g₁ g₂ : X → ℂ} (h₁ : A.HoloOn V g₁) (h₂ : A.HoloOn V g₂)
    (hne : ∀ y ∈ V, g₂ y ≠ 0) : A.HoloOn V (fun y => g₁ y / g₂ y) :=
  fun j w hw => (h₁ j w hw).div (h₂ j w hw) (hne _ hw.2)

theorem pot_holoOn_sum_log {K : Type} [Fintype K] {V : Set X} {g : K → X → ℂ} (m : K → ℤ)
    (r : K → ℝ) (h : ∀ k, A.HoloOn V (g k)) (hs : ∀ k, ∀ y ∈ V, g k y ∈ Complex.slitPlane) :
    A.HoloOn V (fun y => ∑ k, (m k : ℂ) * (Complex.log (g k y) + (r k : ℂ))) := by
  intro j w hw
  have : ∀ k, AnalyticAt ℂ (fun z => (m k : ℂ) *
      (Complex.log (g k ((A.chart j).symm z)) + (r k : ℂ))) w := fun k =>
    analyticAt_const.mul ((AnalyticAt.clog (h k j w hw) (hs k _ hw.2)).add analyticAt_const)
  exact Finset.analyticAt_fun_sum _ fun k _ => this k

end Holo

theorem pot_re_sum_log {K : Type} [Fintype K] (m : K → ℤ) (u v : K → ℂ) (hu : ∀ k, u k ≠ 0)
    (hv : ∀ k, v k ≠ 0) :
    (∑ k, (m k : ℂ) * (Complex.log (u k / v k) + ((Real.log ‖v k‖ : ℝ) : ℂ))).re =
      ∑ k, (m k : ℝ) * Real.log ‖u k‖ := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : (Complex.log (u k / v k) + ((Real.log ‖v k‖ : ℝ) : ℂ)).re = Real.log ‖u k‖ := by
    rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
      Real.log_div (norm_ne_zero_iff.2 (hu k)) (norm_ne_zero_iff.2 (hv k))]
    ring
  simp [Complex.mul_re, h1]

theorem pot_log_h_conj {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (f : HermLine ι)
    (hf : IsConjInvariantH f) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) {a : K → ℂ}
    (ha : ∀ k, a k ≠ 0) :
    Real.log (f.h (fun p => a p.1 * cj z p)) - Real.log (f.h z) =
      ∑ k, (f.a k : ℝ) * Real.log ‖a k‖ := by
  have hP : ∀ k ∈ (Finset.univ : Finset K), ‖a k‖ ^ f.a k ≠ 0 := fun k _ =>
    (zpow_pos (norm_pos_iff.mpr (ha k)) _).ne'
  have hP' : (∏ k, ‖a k‖ ^ f.a k) ≠ 0 := Finset.prod_ne_zero_iff.2 hP
  rw [f.smul a (cj z) ha, show f.h (cj z) = f.h z from hf z,
    Real.log_mul hP' (f.pos z hz).ne', Real.log_prod hP]
  simp [Real.log_zpow]

theorem pot_conj_pluriharmonic : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X} {lift : X → X → (Σ k, ι k) → ℂ}, IsLiftSys A P U lift → ∀ (c : X → X), (∀ x, SameOrbit (lift (c x) (c x)) (cj (lift x x))) → Continuous c → (∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source))) → ∀ (f : HermLine ι), IsConjInvariantH f → ∀ (th : LocPot X), (∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, Real.log (f.h (lift x y)) - th.φ x y = (G y).re) → ∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, th.φ (c x) (c y) - th.φ x y = (G y).re := by
  intro K _ ι _ e X _ A P U lift hL c horb hcc hanti f hf th hth x
  obtain ⟨hUo, hUm, hUh, hUpts, hUor, -, -, -⟩ := hL
  choose i hi using (hUpts x x (hUm x)).1
  obtain ⟨V₁, hV₁o, hxV₁, G₁, hG₁, hφ₁⟩ := hth x
  obtain ⟨V₂, hV₂o, hxV₂, G₂, hG₂, hφ₂⟩ := hth (c x)

  have horbit : ∀ y ∈ U x, c y ∈ U (c x) → ∃ a : K → ℂ, (∀ k, a k ≠ 0) ∧
      lift (c x) (c y) = fun p => a p.1 * cj (lift x y) p := fun y hy hcy =>
    sameOrbit_trans (sameOrbit_trans (hUor (c x) (c y) (c y) ⟨hcy, hUm (c y)⟩) (horb y))
      (sameOrbit_cj (hUor y x y ⟨hUm y, hy⟩))

  let b : K → X → ℂ := fun k y =>
    starRingEnd ℂ (lift (c x) (c y) ⟨k, i k⟩) / lift x y ⟨k, i k⟩
  let D : K → Set X := fun k => U x ∩ (fun y => lift x y ⟨k, i k⟩) ⁻¹' {0}ᶜ
  have hDo : ∀ k, IsOpen (D k) := fun k =>
    (pot_holoOn_continuousOn (hUo x) (hUh x _)).isOpen_inter_preimage (hUo x) isOpen_compl_singleton
  let W₁ : Set X := (U x ∩ c ⁻¹' U (c x)) ∩ ⋂ k, D k
  have hW₁o : IsOpen W₁ :=
    ((hUo x).inter ((hUo (c x)).preimage hcc)).inter (isOpen_iInter_of_finite hDo)
  have hxW₁ : x ∈ W₁ :=
    ⟨⟨hUm x, hUm (c x)⟩, Set.mem_iInter.2 fun k => ⟨hUm x, hi k⟩⟩
  have hden : ∀ y ∈ W₁, ∀ k, lift x y ⟨k, i k⟩ ≠ 0 := fun y hy k =>
    (Set.mem_iInter.1 hy.2 k).2

  have hba : ∀ y ∈ W₁, ∀ a : K → ℂ, lift (c x) (c y) = (fun p => a p.1 * cj (lift x y) p) →
      ∀ k, b k y = starRingEnd ℂ (a k) := fun y hy a ha k => by
    change starRingEnd ℂ (lift (c x) (c y) ⟨k, i k⟩) / lift x y ⟨k, i k⟩ = _
    rw [ha]
    simp only [cj, map_mul, Complex.conj_conj]
    exact mul_div_cancel_right₀ _ (hden y hy k)
  have hbne : ∀ y ∈ W₁, ∀ k, b k y ≠ 0 := fun y hy k => by
    obtain ⟨a, ha, hl⟩ := horbit y hy.1.1 hy.1.2
    rw [hba y hy a hl k]
    simpa using ha k
  have hbH : ∀ k, A.HoloOn W₁ (b k) := fun k =>
    pot_holoOn_div
      (pot_holoOn_mono (GlobalTheory.T.holomorphic_conjugate_pullback c hcc hanti (hUh (c x) ⟨k, i k⟩)) fun y hy => hy.1.2)
      (pot_holoOn_mono (hUh x ⟨k, i k⟩) fun y hy => hy.1.1) fun y hy => hden y hy k
  have hqH : ∀ k, A.HoloOn W₁ (fun y => b k y / b k x) := fun k =>
    pot_holoOn_div (hbH k) (fun j w _ => analyticAt_const) fun _ _ => hbne x hxW₁ k
  let B : K → Set X := fun k => W₁ ∩ (fun y => b k y / b k x) ⁻¹' Metric.ball 1 1
  have hBo : ∀ k, IsOpen (B k) := fun k =>
    (pot_holoOn_continuousOn hW₁o (hqH k)).isOpen_inter_preimage hW₁o Metric.isOpen_ball
  let W₂ : Set X := W₁ ∩ ⋂ k, B k
  let V : Set X := (W₂ ∩ V₁) ∩ c ⁻¹' V₂
  have hVo : IsOpen V :=
    ((hW₁o.inter (isOpen_iInter_of_finite hBo)).inter hV₁o).inter (hV₂o.preimage hcc)
  have hVW : V ⊆ W₁ := fun y hy => hy.1.1.1
  have hxV : x ∈ V := by
    refine ⟨⟨⟨hxW₁, Set.mem_iInter.2 fun k => ⟨hxW₁, ?_⟩⟩, hxV₁⟩, hxV₂⟩
    simp [div_self (hbne x hxW₁ k)]
  have hslit : ∀ k, ∀ y ∈ V, b k y / b k x ∈ Complex.slitPlane := fun k y hy => by
    have h1 : b k y / b k x ∈ Metric.ball (1 : ℂ) 1 := (Set.mem_iInter.1 hy.1.1.2 k).2
    have h2 : ‖b k y / b k x - 1‖ < 1 := by simpa [dist_eq_norm] using h1
    simpa using Complex.mem_slitPlane_of_norm_lt_one h2
  refine ⟨V, hVo, hxV,
    fun y => G₁ y - starRingEnd ℂ (G₂ (c y)) +
      ∑ k, (f.a k : ℂ) * (Complex.log (b k y / b k x) + ((Real.log ‖b k x‖ : ℝ) : ℂ)), ?_, ?_⟩
  · refine pot_holoOn_sub_add (pot_holoOn_mono hG₁ fun y hy => hy.1.2)
      (pot_holoOn_mono (GlobalTheory.T.holomorphic_conjugate_pullback c hcc hanti hG₂) fun y hy => hy.2) ?_
    exact pot_holoOn_sum_log f.a _ (fun k => pot_holoOn_mono (hqH k) hVW) fun k => hslit k
  · intro y hy
    have hyW := hVW hy
    obtain ⟨a, ha, hl⟩ := horbit y hyW.1.1 hyW.1.2
    have e₁ := hφ₁ y hy.1.2
    have e₂ := hφ₂ (c y) hy.2
    have e₃ := pot_log_h_conj f hf (hUpts x y hyW.1.1).1 ha
    rw [← hl] at e₃
    have e₄ := pot_re_sum_log f.a (fun k => b k y) (fun k => b k x) (hbne y hyW) (hbne x hxW₁)
    have e₅ : ∑ k, (f.a k : ℝ) * Real.log ‖b k y‖ = ∑ k, (f.a k : ℝ) * Real.log ‖a k‖ :=
      Finset.sum_congr rfl fun k _ => by rw [hba y hyW a hl k, RCLike.norm_conj]
    simp only [Complex.add_re, Complex.sub_re, Complex.conj_re]
    rw [e₄, e₅, ← e₃]
    linarith

end GlobalTheory.CompanionTheory.Ar.PB.Cj
