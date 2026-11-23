import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBlocks
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FA

namespace BlockPot

theorem continuousAt_of_holoOn {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {U : Set X}
    {g : X → ℂ} (hg : A.HoloOn U g) {x : X} (hx : x ∈ U) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  have an := hg j (A.chart j x) ⟨(A.chart j).map_source hj, by
    simpa only [Set.mem_preimage, (A.chart j).left_inv hj] using hx⟩
  have c : ContinuousAt (fun y => (g ∘ (A.chart j).symm) (A.chart j y)) x :=
    ContinuousAt.comp (f := A.chart j) an.continuousAt ((A.chart j).continuousAt hj)
  refine c.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp only [Function.comp_apply, (A.chart j).left_inv hy]

theorem holoOn_comp {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : FinHolAtlas e' X} {B : FinHolAtlas e Y} {h : Y → X} (hh : HoloMap B A h) {S : Set X}
    {g : X → ℂ} (hg : A.HoloOn S g) : B.HoloOn (h ⁻¹' S) (fun y => g (h y)) := by
  intro j u hu
  obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm u))
  have hτ : AnalyticAt ℂ (A.chart k ∘ h ∘ (B.chart j).symm) u := hh.2 j k u ⟨hu.1, hk⟩
  have hgu : AnalyticAt ℂ (g ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (B.chart j).symm) u) :=
    hg k _ ⟨(A.chart k).map_source hk, by
      simpa only [Function.comp_apply, Set.mem_preimage, (A.chart k).left_inv hk] using hu.2⟩
  refine (hgu.comp hτ).congr ?_
  filter_upwards [((B.chart j).isOpen_inter_preimage_symm ((A.chart k).open_source.preimage hh.1)).mem_nhds
    ⟨hu.1, hk⟩] with y' hy'
  simp only [Function.comp_apply, (A.chart k).left_inv hy'.2]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K' : Type} [Fintype K']
  {ι' : K' → Type} [∀ k, Fintype (ι' k)] {κ : K' → K} {v : (Σ k, ι' k) → Σ k, ι k}

theorem sum_block (hb : IsBlockMap κ v) (z : (Σ k, ι k) → ℂ) (k : K') :
    ∑ i, ‖z ⟨κ k, i⟩‖ ^ 2 = ∑ m, ‖z (v ⟨k, m⟩)‖ ^ 2 := by
  obtain ⟨hκ, hv, h1, h2⟩ := hb
  have hS : (Finset.univ.image fun i : ι (κ k) => (⟨κ k, i⟩ : Σ k, ι k)) =
      Finset.univ.image fun m : ι' k => v ⟨k, m⟩ := by
    ext q
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨⟨k', m⟩, hp⟩ := h2 ⟨κ k, i⟩ ⟨k, rfl⟩
      have hk : k' = k := hκ (by simpa [hp] using (h1 ⟨k', m⟩).symm)
      subst hk
      exact ⟨m, hp⟩
    · rintro ⟨m, rfl⟩
      rcases hq : v ⟨k, m⟩ with ⟨a, b⟩
      have : a = κ k := by simpa [hq] using h1 ⟨k, m⟩
      subst this
      exact ⟨b, rfl⟩
  have e1 := Finset.sum_image (s := Finset.univ) (g := fun i : ι (κ k) => (⟨κ k, i⟩ : Σ k, ι k))
    (f := fun q => ‖z q‖ ^ 2) (fun a _ b _ hab => by simpa using hab)
  have e2 := Finset.sum_image (s := Finset.univ) (g := fun m : ι' k => v ⟨k, m⟩)
    (f := fun q => ‖z q‖ ^ 2) (fun a _ b _ hab => by simpa using hv hab)
  rw [← e1, hS, e2]

theorem refNorm_block (hb : IsBlockMap κ v) {a : K → ℤ} (ha : ∀ k, k ∉ Set.range κ → a k = 0)
    (z : (Σ k, ι k) → ℂ) : refNorm a z = refNorm (fun k => a (κ k)) (z ∘ v) := by
  unfold refNorm
  symm
  refine Fintype.prod_of_injective κ hb.1 _ _ (fun k hk => ?_) (fun k => ?_)
  · simp [ha k hk]
  · simp only [Function.comp_apply]
    rw [sum_block hb z k]

theorem orbit_near {P J : Ideal (MRing ι)} {P' J' : Ideal (MRing ι')} {e e' : ℕ} (R : AnLogRes P J e)
    (R' : AnLogRes P' J' e') (h : R.X → R'.X) (hb : IsBlockMap κ v)
    (hO : ∀ x, SameOrbit (R'.lift (h x) (h x)) (R.lift x x ∘ v)) {x y : R.X} (hy : y ∈ R.U x)
    (hy' : h y ∈ R'.U (h x)) :
    ∃ c : K' → ℂ, (∀ k, c k ≠ 0) ∧ ∀ p, R'.lift (h x) (h y) p = c p.1 * R.lift x y (v p) := by
  obtain ⟨c₁, hc₁, e₁⟩ := R'.compat (h x) (h y) (h y) ⟨hy', R'.mem_U _⟩
  obtain ⟨c₂, hc₂, e₂⟩ := hO y
  obtain ⟨c₃, hc₃, e₃⟩ := R.compat x y y ⟨hy, R.mem_U _⟩
  refine ⟨fun k => c₁ k * c₂ k * (c₃ (κ k))⁻¹, fun k => mul_ne_zero (mul_ne_zero (hc₁ k) (hc₂ k))
    (inv_ne_zero (hc₃ _)), fun p => ?_⟩
  have f₁ := congrFun e₁ p
  have f₂ := congrFun e₂ p
  have f₃ := congrFun e₃ (v p)
  have f₃' : R.lift x y (v p) = c₃ (κ p.1) * R.lift y y (v p) := by
    rw [← hb.2.2.1 p]
    exact f₃
  have hc : c₃ (κ p.1) ≠ 0 := hc₃ _
  simp only [Function.comp_apply] at f₂
  rw [f₁, f₂, f₃']
  field_simp

theorem samePot_block (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K']
    (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K' → K) (v : (Σ k, ι' k) → Σ k, ι k) (P J : Ideal (MRing ι))
    (P' J' : Ideal (MRing ι')) (e e' : ℕ) (R : AnLogRes P J e) (R' : AnLogRes P' J' e') (h : R.X → R'.X)
    (hh : HoloMap R.A R'.A h) (a : K → ℤ) (hb : IsBlockMap κ v) (ha : ∀ k, k ∉ Set.range κ → a k = 0)
    (hO : ∀ x, SameOrbit (R'.lift (h x) (h x)) (R.lift x x ∘ v)) :
    SamePot R.A Set.univ (potOf R (fsHerm ι a)) ((potOf R' (fsHerm ι' fun k => a (κ k))).pullback h hh.1) := by
  intro x _
  have hxU : x ∈ R.U x := R.mem_U x
  have hxU' : h x ∈ R'.U (h x) := R'.mem_U _

  obtain ⟨cx, hcx, ex⟩ := orbit_near R R' h hb hO hxU hxU'
  have hm : ∀ k : K', ∃ m : ι' k, R.lift x x (v ⟨k, m⟩) ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := (R.mem x x hxU).1 (κ k)
    obtain ⟨⟨k', m⟩, hp⟩ := hb.2.2.2 ⟨κ k, i⟩ ⟨k, rfl⟩
    have hk : k' = k := hb.1 (by simpa [hp] using (hb.2.2.1 ⟨k', m⟩).symm)
    subst hk
    exact ⟨m, by rw [hp]; exact hi⟩
  choose m hm using hm

  let den : K' → R.X → ℂ := fun k y => R.lift x y (v ⟨k, m k⟩)
  let num : K' → R.X → ℂ := fun k y => R'.lift (h x) (h y) ⟨k, m k⟩
  let rat : K' → R.X → ℂ := fun k y => num k y / den k y / cx k
  have hdenH : ∀ k, R.A.HoloOn (R.U x) (den k) := fun k => R.holo x _
  have hnumH : ∀ k, R.A.HoloOn (h ⁻¹' R'.U (h x)) (num k) := fun k =>
    holoOn_comp hh (R'.holo (h x) ⟨k, m k⟩)
  have hdenC : ∀ k, ContinuousAt (den k) x := fun k => continuousAt_of_holoOn (hdenH k) hxU
  have hnumC : ∀ k, ContinuousAt (num k) x := fun k => continuousAt_of_holoOn (hnumH k) hxU'
  have hratC : ∀ k, ContinuousAt (rat k) x := fun k =>
    ((hnumC k).div (hdenC k) (hm k)).div continuousAt_const (hcx k)
  have hrat1 : ∀ k, rat k x = 1 := by
    intro k
    have := ex ⟨k, m k⟩
    have h1 : den k x ≠ 0 := hm k
    have h2 := hcx k
    simp only [rat, num, den] at h1 ⊢
    rw [this]
    field_simp
  have hev : ∀ᶠ y in 𝓝 x, y ∈ R.U x ∧ h y ∈ R'.U (h x) ∧ ∀ k, den k y ≠ 0 ∧ rat k y ∈ Complex.slitPlane := by
    have e1 : ∀ᶠ y in 𝓝 x, y ∈ R.U x := (R.isOpen_U x).mem_nhds hxU
    have e2 : ∀ᶠ y in 𝓝 x, h y ∈ R'.U (h x) := ((R'.isOpen_U (h x)).preimage hh.1).mem_nhds hxU'
    have e3 : ∀ᶠ y in 𝓝 x, ∀ k, den k y ≠ 0 ∧ rat k y ∈ Complex.slitPlane := by
      refine eventually_all.2 fun k => ((hdenC k).eventually_ne (hm k)).and ?_
      exact (hratC k).eventually_mem (Complex.isOpen_slitPlane.mem_nhds (by
        simpa only [hrat1 k] using Complex.one_mem_slitPlane))
    exact e1.and (e2.and e3)
  obtain ⟨V, hVs, hVo, hxV⟩ := mem_nhds_iff.1 hev
  refine ⟨V, hVo, hxV, fun y => -∑ k, (a (κ k) : ℂ) * (Complex.log (rat k y) + (Real.log ‖cx k‖ : ℂ)), ?_, ?_⟩
  · intro j u hu
    obtain ⟨hy1, hy2, hy3⟩ := hVs hu.2
    have hd : ∀ k, AnalyticAt ℂ (fun u => den k ((R.A.chart j).symm u)) u := fun k =>
      hdenH k j u ⟨hu.1, hy1⟩
    have hn : ∀ k, AnalyticAt ℂ (fun u => num k ((R.A.chart j).symm u)) u := fun k =>
      hnumH k j u ⟨hu.1, hy2⟩
    have hr : ∀ k, AnalyticAt ℂ (fun u => rat k ((R.A.chart j).symm u)) u := fun k =>
      ((hn k).div (hd k) (hy3 k).1).div analyticAt_const (hcx k)
    have hl : ∀ k, AnalyticAt ℂ (fun u => (a (κ k) : ℂ) * (Complex.log (rat k ((R.A.chart j).symm u)) +
        (Real.log ‖cx k‖ : ℂ))) u := fun k =>
      analyticAt_const.mul (((hr k).clog (hy3 k).2).add analyticAt_const)
    exact (Finset.analyticAt_fun_sum Finset.univ fun k _ => hl k).neg
  · intro y hy
    obtain ⟨hy1, hy2, hy3⟩ := hVs hy
    obtain ⟨c, hc, ec⟩ := orbit_near R R' h hb hO hy1 hy2
    have hw : R'.lift (h x) (h y) = torusSmul c (R.lift x y ∘ v) := by
      funext p
      simpa [torusSmul] using ec p
    have hrat : ∀ k, rat k y = c k / cx k := by
      intro k
      have h1 : den k y ≠ 0 := (hy3 k).1
      have h2 := ec ⟨k, m k⟩
      simp only [rat, num, den] at h1 ⊢
      rw [h2]
      field_simp
    have hpos : 0 < refNorm a (R.lift x y) := refNorm_pos a (R.mem x y hy1).1
    have hprod : (∏ k, ‖c k‖ ^ a (κ k)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
    have hL : Real.log (refNorm (fun k => a (κ k)) (R'.lift (h x) (h y))) =
        (∑ k, (a (κ k) : ℝ) * Real.log ‖c k‖) + Real.log (refNorm a (R.lift x y)) := by
      rw [hw, refNorm_smul, ← refNorm_block hb ha, Real.log_mul hprod hpos.ne', Real.log_prod]
      · simp only [Real.log_zpow]
      · exact fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
    have hG : (-∑ k, (a (κ k) : ℂ) * (Complex.log (rat k y) + (Real.log ‖cx k‖ : ℂ))).re =
        -∑ k, (a (κ k) : ℝ) * Real.log ‖c k‖ := by
      rw [Complex.neg_re, Complex.re_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      have hck := norm_ne_zero_iff.2 (hc k)
      have hcxk := norm_ne_zero_iff.2 (hcx k)
      have hcast : ((a (κ k) : ℤ) : ℂ) = (((a (κ k) : ℤ) : ℝ) : ℂ) := by push_cast; rfl
      rw [hrat k, hcast, Complex.re_ofReal_mul, Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
        Real.log_div hck hcxk]
      ring
    show Real.log (refNorm a (R.lift x y)) - Real.log (refNorm (fun k => a (κ k)) (R'.lift (h x) (h y))) = _
    rw [hL, hG]
    ring

end BlockPot

end GlobalTheory.CompanionTheory.Ar.PB.FA
