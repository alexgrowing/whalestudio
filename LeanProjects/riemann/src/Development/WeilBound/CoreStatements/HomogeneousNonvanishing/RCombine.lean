import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.IsOpenHoloPreimage
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.RSnc
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.REnlarge
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.FderivAffCoordZero
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularWeightMonotoneRegularizationStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

namespace RC

open HolomorphicMinorCharts

variable {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem section_pull {A : FinHolAtlas e X} {B : FinHolAtlas e' Y} {π : Y → X} (h : HoloMap B A π) {L : LocPot X}
    {s : X → X → ℂ} (hs : IsSection A L s) : IsSection B (L.pullback π h.1) fun x y => s (π x) (π y) :=
  ⟨fun x => holo_comp_map h (hs.1 (π x)), fun x x' y hy => hs.2 (π x) (π x') (π y) hy⟩

theorem nrm_mul (L L' : LocPot X) (s s' : X → X → ℂ) (x y : X) :
    ‖s x y * s' x y‖ * Real.exp (-(L + L').φ x y) =
      (‖s x y‖ * Real.exp (-L.φ x y)) * (‖s' x y‖ * Real.exp (-L'.φ x y)) := by
  rw [add_φ, norm_mul, neg_add, Real.exp_add]
  ring

theorem section_mul {A : FinHolAtlas e X} {L L' : LocPot X} {s s' : X → X → ℂ} (hs : IsSection A L s)
    (hs' : IsSection A L' s') : IsSection A (L + L') fun x y => s x y * s' x y := by
  refine ⟨fun x j w hw => (hs.1 x j w ⟨hw.1, hw.2.1⟩).mul (hs'.1 x j w ⟨hw.1, hw.2.2⟩), fun x x' y hy => ?_⟩
  rw [nrm_mul, nrm_mul, hs.2 x x' y ⟨hy.1.1, hy.2.1⟩, hs'.2 x x' y ⟨hy.1.2, hy.2.2⟩]

theorem log_mul_le {L L' : LocPot X} {s s' : X → X → ℂ} (h : ∀ y, logNormSec L s y ≤ 0)
    (h' : ∀ y, logNormSec L' s' y ≤ 0) (y : X) : logNormSec (L + L') (fun x y => s x y * s' x y) y ≤ 0 := by
  have h1 := h y
  have h2 := h' y
  unfold logNormSec at *
  rw [Real.log_nonpos_iff (by positivity)] at *
  rw [nrm_mul]
  exact mul_le_one₀ h1 (by positivity) h2

theorem log_mul_eq {L L' : LocPot X} {s s' : X → X → ℂ} {y : X} (hy : y ∉ bdry fun x y => s x y * s' x y) :
    logNormSec (L + L') (fun x y => s x y * s' x y) y = logNormSec L s y + logNormSec L' s' y := by
  have h1 : s y y * s' y y ≠ 0 := hy
  unfold logNormSec
  rw [nrm_mul, Real.log_mul (mul_ne_zero (norm_ne_zero_iff.mpr (left_ne_zero_of_mul h1)) (Real.exp_pos _).ne')
    (mul_ne_zero (norm_ne_zero_iff.mpr (right_ne_zero_of_mul h1)) (Real.exp_pos _).ne')]

theorem exists_scale [CompactSpace X] {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ} (hL : IsPotential A L)
    (hs : IsSection A L s) : ∃ L' : LocPot X, IsPotential A L' ∧ IsSection A L' s ∧ ∀ y, logNormSec L' s y ≤ 0 := by
  have hc : Continuous fun y => ‖s y y‖ * Real.exp (-L.φ y y) := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    refine ContinuousAt.congr (((holo_continuousAt (hs.1 x) (L.mem_U x)).norm).mul
      (CSnc.smooth_continuousAt (L.isOpen_U x) (hL.1 x) (L.mem_U x)).neg.rexp) ?_
    filter_upwards [(L.isOpen_U x).mem_nhds (L.mem_U x)] with y hy
    exact hs.2 x y y ⟨hy, L.mem_U y⟩
  obtain ⟨M, hM⟩ := (isCompact_range hc).bddAbove
  have hsm : A.Smooth fun _ => M := fun j => contDiffOn_const
  have key : ∀ x y, ‖s x y‖ * Real.exp (-(L + LocPot.ofFun fun _ => M).φ x y) =
      ‖s x y‖ * Real.exp (-L.φ x y) * Real.exp (-M) := fun x y => by
    rw [add_φ, neg_add, Real.exp_add, mul_assoc]
    rfl
  refine ⟨L + LocPot.ofFun fun _ => M, isPotentialAdd A _ _ hL (isPotential_ofFun A _ hsm),
    ⟨fun x => holo_mono (hs.1 x) fun y hy => hy.1, fun x x' y hy => ?_⟩, fun y => ?_⟩
  · rw [key, key, hs.2 x x' y ⟨hy.1.1, hy.2.1⟩]
  · unfold logNormSec
    rw [Real.log_nonpos_iff (by positivity), key, Real.exp_neg M, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    have h1 : ‖s y y‖ * Real.exp (-L.φ y y) ≤ M := hM ⟨y, rfl⟩
    have := Real.add_one_le_exp M
    linarith

theorem exists_line {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (b : K → ℤ) :
    ∃ L : HermLine ι, IsSmoothHerm L ∧ L.a = b := by
  refine ⟨HermLine.ofMetrics (fun k => fsMetric (ι k)) b, ?_, rfl⟩
  change ContDiffOn ℝ _ (fun z => ∏ k, (fsMetric (ι k)).ρ (GP.blk (ι := ι) k z) ^ b k) _
  refine contDiffOn_prod fun k _ z hz => ContDiffAt.contDiffWithinAt ?_
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (fsMetric (ι k)).ρ (GP.blk (ι := ι) k z)) z :=
    ContDiffAt.comp (g := (fsMetric (ι k)).ρ) z (GP.contDiffAt_fs (GP.blk_ne hz k))
      ((GP.blk (ι := ι) k).contDiff.restrict_scalars ℝ).contDiffAt
  have h2 := ((fsMetric (ι k)).pos _ (GP.blk_ne hz k)).ne'
  rcases b k with n | n
  · simpa using h1.pow n
  · simp only [zpow_negSucc]
    exact (h1.pow (n + 1)).inv (pow_ne_zero _ h2)

theorem one (hPull : PullbackStatement) {D : ℕ} [CompactSpace Y] [T2Space Y] {B : FinHolAtlas D Y} {Θ : LocPot Y}
    (hΘ : IsPotential B Θ) (hΘ' : IsPosPot B Θ) {σ : Type} (S : AnSys D σ) {π : Y → S.X} (h : HoloMap B S.A π)
    {n : ℕ} {m : Fin n → ℕ} {W : Fin n → Set Y}
    (hsnc : IsSNC B (S.L.pullback π h.1) (fun x y => S.s (π x) (π y)) m W) {L : LocPot Y} {s : Y → Y → ℂ}
    (hb : bdry (fun x y => S.s (π x) (π y)) ⊆ bdry s)
    (hr : ∀ y, y ∉ bdry s → rW (S.L.pullback π h.1) (fun x y => S.s (π x) (π y)) y ≤ rW L s y) (a : σ) :
    ∃ C' t' : ℝ, 0 < t' ∧ ∀ C₅ C t₀ : ℝ, 0 ≤ C₅ → S.C₅ ≤ C₅ → |C'| ≤ C → 0 < t₀ → t₀ ≤ t' → t₀ ≤ Real.exp (-1) →
      IsSingWeight B L s ((S.th a).pullback π h.1) (S.ph a ∘ π) C₅ ∧
      IsRegFamily B Θ L s ((S.th a).pullback π h.1) (S.ph a ∘ π) (fun t => S.phT a t ∘ π) C t₀ ∧
      IsRegFamilyC2 B s (S.ph a ∘ π) (fun t => S.phT a t ∘ π) := by
  obtain ⟨C', t', h1, h2, h3⟩ := hPull S.A B π h S.Θ S.L Θ S.s S.m S.W m W S.potΘ S.posΘ hΘ hΘ' S.potL S.sec S.snc
    S.norm_le hsnc (S.th a) (S.ph a) (S.phT a) S.C₅ S.C S.t₀ (S.sing a) (S.reg a) (S.c2 a)
  have hn : ∀ y, logNormSec (S.L.pullback π h.1) (fun x y => S.s (π x) (π y)) y ≤ 0 := fun y => S.norm_le (π y)
  obtain ⟨m1, m2, -⟩ := GlobalTheory.T.singular_weight_monotone_regularization D Y B Θ _ _ n m W (isPotentialPullback S.A B π h _ S.potL)
    (section_pull h S.sec) hsnc hn hΘ hΘ'
  refine ⟨C', t', h2.1, fun C₅ C t₀ a1 a2 a3 a4 a5 a6 => ?_⟩
  exact r_enlarge D Y B Θ _ L _ s _ _ _ C₅ C t₀ a1 ((abs_nonneg _).trans a3) a6 hn hb hr (m1 _ _ _ _ a2 h1)
    (m2 _ _ _ _ _ _ _ a3 a4 a5 a6 h2 h1.1) h3

end RC

open RC HolomorphicMinorCharts in
theorem r_combine : PullbackStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P J D) (Amp : HermLine ι) (β : MRing ι) (b : K → ℕ) (σ : Type) [Fintype σ] (S₁ S₂ : AnSys D σ) (π₁ : R.X → S₁.X) (π₂ : R.X → S₂.X) (h₁ : HoloMap R.A S₁.A π₁) (h₂ : HoloMap R.A S₂.A π₂), IsPotential R.A (potOf R Amp) → IsPosPot R.A (potOf R Amp) → IsMultiHomog β b → β ∉ P → (∀ z ∈ mcPts P, evC z β = 0 → z ∈ mcPts J) → (∀ x, π₁ x ∈ bdry S₁.s → evC (R.lift x x) β = 0) → (∀ x, π₂ x ∈ bdry S₂.s → evC (R.lift x x) β = 0) → ∃ (L : LocPot R.X) (s : R.X → R.X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set R.X) (C₅ C t₀ : ℝ), IsPotential R.A L ∧ IsSection R.A L s ∧ IsSNC R.A L s m W ∧ (∀ y, logNormSec L s y ≤ 0) ∧ (∀ x, x ∈ bdry s ↔ evC (R.lift x x) β = 0) ∧ t₀ ≤ S₁.t₀ ∧ t₀ ≤ S₂.t₀ ∧ (∀ a, IsSingWeight R.A L s ((S₁.th a).pullback π₁ h₁.1) (S₁.ph a ∘ π₁) C₅ ∧ IsRegFamily R.A (potOf R Amp) L s ((S₁.th a).pullback π₁ h₁.1) (S₁.ph a ∘ π₁) (fun t => S₁.phT a t ∘ π₁) C t₀ ∧ IsRegFamilyC2 R.A s (S₁.ph a ∘ π₁) (fun t => S₁.phT a t ∘ π₁)) ∧ ∀ a, IsSingWeight R.A L s ((S₂.th a).pullback π₂ h₂.1) (S₂.ph a ∘ π₂) C₅ ∧ IsRegFamily R.A (potOf R Amp) L s ((S₂.th a).pullback π₂ h₂.1) (S₂.ph a ∘ π₂) (fun t => S₂.phT a t ∘ π₂) C t₀ ∧ IsRegFamilyC2 R.A s (S₂.ph a ∘ π₂) (fun t => S₂.phT a t ∘ π₂) := by
  intro hPull K _ ι _ P J D R Amp β b σ _ S₁ S₂ π₁ π₂ h₁ h₂ hΘ hΘ' hβ hβP hβJ hb₁ hb₂
  obtain ⟨n₀, m₀, W₀, hsnc₀⟩ := R.snc β b hβP hβ hβJ
  have hsnc : ∀ (L : LocPot R.X) (s : R.X → R.X → ℂ), IsPotential R.A L → IsSection R.A L s →
      (∀ x ∈ bdry s, evC (R.lift x x) β = 0) → ∃ (n : ℕ) (m : Fin n → ℕ) (W : Fin n → Set R.X), IsSNC R.A L s m W :=
    fun L s hL hs hb => r_snc D R.X R.A _ _ n₀ m₀ W₀ L s hsnc₀ hL hs hb
      fun x x' y hy => eval_ne_so hβ (R.compat x x' y hy)
  obtain ⟨Lb, hLb, hLa⟩ := exists_line (ι := ι) fun k => (b k : ℤ)
  obtain ⟨L₃, p₃, s₃, l₃⟩ := exists_scale (isPotential_potOf R hLb)
    (isSection_lift R (A := Lb) (s := β) ⟨b, fun k => congrFun hLa k, hβ, hβP⟩)
  have p₁ := isPotentialPullback S₁.A R.A π₁ h₁ _ S₁.potL
  have p₂ := isPotentialPullback S₂.A R.A π₂ h₂ _ S₂.potL
  have s₁ := section_pull h₁ S₁.sec
  have s₂ := section_pull h₂ S₂.sec
  have l₁ : ∀ y, logNormSec (S₁.L.pullback π₁ h₁.1) (fun x y => S₁.s (π₁ x) (π₁ y)) y ≤ 0 :=
    fun y => S₁.norm_le (π₁ y)
  have l₂ : ∀ y, logNormSec (S₂.L.pullback π₂ h₂.1) (fun x y => S₂.s (π₂ x) (π₂ y)) y ≤ 0 :=
    fun y => S₂.norm_le (π₂ y)
  obtain ⟨n₁, m₁, W₁, c₁⟩ := hsnc _ _ p₁ s₁ hb₁
  obtain ⟨n₂, m₂, W₂, c₂⟩ := hsnc _ _ p₂ s₂ hb₂
  have p := isPotentialAdd R.A _ _ (isPotentialAdd R.A _ _ p₁ p₂) p₃
  have sec := section_mul (section_mul s₁ s₂) s₃
  set L := S₁.L.pullback π₁ h₁.1 + S₂.L.pullback π₂ h₂.1 + L₃ with hL
  set s : R.X → R.X → ℂ := fun x y => S₁.s (π₁ x) (π₁ y) * S₂.s (π₂ x) (π₂ y) *
    eval (R.lift x y) (map (Int.castRingHom ℂ) β) with hs
  have hbd : ∀ x, x ∈ bdry s ↔ evC (R.lift x x) β = 0 := fun x => by
    refine ⟨fun h => ?_, fun h => mul_eq_zero_of_right _ h⟩
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact hb₁ x h
      · exact hb₂ x h
    · exact h
  obtain ⟨n, m, W, c⟩ := hsnc L s p sec fun x => (hbd x).mp
  have hlog : ∀ y, y ∉ bdry s → logNormSec L s y =
      logNormSec (S₁.L.pullback π₁ h₁.1) (fun x y => S₁.s (π₁ x) (π₁ y)) y +
      logNormSec (S₂.L.pullback π₂ h₂.1) (fun x y => S₂.s (π₂ x) (π₂ y)) y +
      logNormSec L₃ (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) β)) y := fun y hy => by
    have h0 : S₁.s (π₁ y) (π₁ y) * S₂.s (π₂ y) (π₂ y) * eval (R.lift y y) (map (Int.castRingHom ℂ) β) ≠ 0 := hy
    rw [← log_mul_eq (s := fun x y => S₁.s (π₁ x) (π₁ y)) (s' := fun x y => S₂.s (π₂ x) (π₂ y))
      (left_ne_zero_of_mul h0)]
    exact log_mul_eq (s := fun x y => S₁.s (π₁ x) (π₁ y) * S₂.s (π₂ x) (π₂ y))
      (s' := fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) β)) hy
  choose C₁ t₁ ht₁ H₁ using one hPull hΘ hΘ' S₁ h₁ c₁ (L := L) (s := s) (fun x hx => (hbd x).mpr (hb₁ x hx))
    fun y hy => by
      have := hlog y hy
      have := l₂ y
      have := l₃ y
      unfold rW
      linarith
  choose C₂ t₂ ht₂ H₂ using one hPull hΘ hΘ' S₂ h₂ c₂ (L := L) (s := s) (fun x hx => (hbd x).mpr (hb₂ x hx))
    fun y hy => by
      have := hlog y hy
      have := l₁ y
      have := l₃ y
      unfold rW
      linarith
  obtain ⟨δ, hδ, hδe, hδ₁, hδ₂⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ Real.exp (-1) ∧ (∀ a, δ ≤ t₁ a) ∧ ∀ a, δ ≤ t₂ a := by
    have e0 : ∀ t : ℝ, 0 < t → ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ≤ t := fun t ht => by
      filter_upwards [Ioc_mem_nhdsGT ht] with δ h using h.2
    exact ((eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)).and ((e0 _ (Real.exp_pos _)).and
      ((eventually_all.mpr fun a => e0 _ (ht₁ a)).and (eventually_all.mpr fun a => e0 _ (ht₂ a))))).exists
  have hpos : σ → 0 < min (min S₁.t₀ S₂.t₀) δ := fun a => lt_min (lt_min (S₁.reg a).1 (S₂.reg a).1) hδ
  have n1 : 0 ≤ ∑ a, |C₁ a| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have n2 : 0 ≤ ∑ a, |C₂ a| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨L, s, n, m, W, max (max S₁.C₅ S₂.C₅) 0, ∑ a, |C₁ a| + ∑ a, |C₂ a|, min (min S₁.t₀ S₂.t₀) δ, p, sec, c,
    log_mul_le (log_mul_le l₁ l₂) l₃, hbd, (min_le_left _ _).trans (min_le_left _ _),
    (min_le_left _ _).trans (min_le_right _ _), fun a => H₁ a _ _ _ (le_max_right _ _)
      ((le_max_left _ _).trans (le_max_left _ _)) ?_ (hpos a) ((min_le_right _ _).trans (hδ₁ a))
      ((min_le_right _ _).trans hδe), fun a => H₂ a _ _ _ (le_max_right _ _)
      ((le_max_right _ _).trans (le_max_left _ _)) ?_ (hpos a) ((min_le_right _ _).trans (hδ₂ a))
      ((min_le_right _ _).trans hδe)⟩
  · have := Finset.single_le_sum (f := fun a => |C₁ a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
    linarith
  · have := Finset.single_le_sum (f := fun a => |C₂ a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
    linarith

end PositivityTheory.UnitarySelfGeneration
