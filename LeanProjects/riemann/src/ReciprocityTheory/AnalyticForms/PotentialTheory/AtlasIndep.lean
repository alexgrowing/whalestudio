import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X]

def unionAtlas (A B : FinHolAtlas e X) (h : A.Compatible B) : FinHolAtlas e X where
  n := A.n + B.n
  chart := Fin.append A.chart B.chart
  cover x := by
    obtain ⟨j, hj⟩ := A.cover x
    exact ⟨Fin.castAdd B.n j, by simpa using hj⟩
  holo j k := by
    induction j using Fin.addCases with
    | left j =>
      induction k using Fin.addCases with
      | left k => simpa [Fin.append_left] using A.holo j k
      | right k => simpa [Fin.append_left, Fin.append_right] using h.1 j k
    | right j =>
      induction k using Fin.addCases with
      | left k => simpa [Fin.append_left, Fin.append_right] using h.2 j k
      | right k => simpa [Fin.append_right] using B.holo j k

@[simp] theorem unionAtlas_chart_castAdd (A B : FinHolAtlas e X) (h : A.Compatible B)
    (j : Fin A.n) : (unionAtlas A B h).chart (Fin.castAdd B.n j) = A.chart j := by
  show Fin.append A.chart B.chart (Fin.castAdd B.n j) = A.chart j
  exact Fin.append_left _ _ _

@[simp] theorem unionAtlas_chart_natAdd (A B : FinHolAtlas e X) (h : A.Compatible B)
    (k : Fin B.n) : (unionAtlas A B h).chart (Fin.natAdd A.n k) = B.chart k := by
  show Fin.append A.chart B.chart (Fin.natAdd A.n k) = B.chart k
  exact Fin.append_right _ _ _

theorem FinHolAtlas.Compatible.symm' {A B : FinHolAtlas e X} (h : A.Compatible B) :
    B.Compatible A := ⟨h.2, h.1⟩

theorem compat_local {A B : FinHolAtlas e X} (h : A.Compatible B) (j : Fin B.n) {y : Fin e → ℂ}
    (hy : y ∈ (B.chart j).target) :
    ∃ k : Fin A.n, AnalyticAt ℂ (A.chart k ∘ (B.chart j).symm) y ∧
      (A.chart k ((B.chart j).symm y)) ∈ (A.chart k).target ∧
      (A.chart k).symm (A.chart k ((B.chart j).symm y)) = (B.chart j).symm y ∧
      ∀ {β : Type} (f : X → β), (f ∘ (B.chart j).symm) =ᶠ[𝓝 y]
        (f ∘ (A.chart k).symm) ∘ (A.chart k ∘ (B.chart j).symm) := by
  obtain ⟨k, hk⟩ := A.cover ((B.chart j).symm y)
  have hmem : y ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' (A.chart k).source := ⟨hy, hk⟩
  have hopen : IsOpen ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (A.chart k).source) :=
    (B.chart j).isOpen_inter_preimage_symm (A.chart k).open_source
  refine ⟨k, h.2 j k y hmem, (A.chart k).map_source hk, (A.chart k).left_inv hk, fun f => ?_⟩
  filter_upwards [hopen.mem_nhds hmem] with y' hy'
  simp only [Function.comp_apply, (A.chart k).left_inv hy'.2]

theorem smoothOn_of_compatible {A B : FinHolAtlas e X} (h : A.Compatible B) {U : Set X}
    (hU : IsOpen U) {f : X → ℝ} (hf : A.SmoothOn U f) : B.SmoothOn U f := by
  intro j y hy
  obtain ⟨k, hT, hTt, hTs, hev⟩ := compat_local h j hy.1
  have hTs' : (A.chart k).symm ((A.chart k) ((B.chart j).symm y)) ∈ U := by
    rw [hTs]
    exact hy.2
  have hopen : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' U) :=
    (A.chart k).isOpen_inter_preimage_symm hU
  have h1 : ContDiffAt ℝ ∞ (f ∘ (A.chart k).symm) ((A.chart k ∘ (B.chart j).symm) y) :=
    (hf k).contDiffAt (hopen.mem_nhds ⟨hTt, hTs'⟩)
  have h2 : ContDiffAt ℝ ∞ (A.chart k ∘ (B.chart j).symm) y :=
    (hT.contDiffAt (n := ∞)).restrict_scalars ℝ
  exact ((h1.comp y h2).congr_of_eventuallyEq (hev f)).contDiffWithinAt

theorem holoOn_of_compatible {A B : FinHolAtlas e X} (h : A.Compatible B) {U : Set X}
    (hU : IsOpen U) {g : X → ℂ} (hg : A.HoloOn U g) : B.HoloOn U g := by
  intro j y hy
  obtain ⟨k, hT, hTt, hTs, hev⟩ := compat_local h j hy.1
  have hTs' : (A.chart k).symm ((A.chart k) ((B.chart j).symm y)) ∈ U := by
    rw [hTs]
    exact hy.2
  exact (AnalyticAt.comp (g := g ∘ (A.chart k).symm) (f := A.chart k ∘ (B.chart j).symm)
    (hg k _ ⟨hTt, hTs'⟩) hT).congr (hev g).symm

theorem isPotential_of_compatible {A B : FinHolAtlas e X} (h : A.Compatible B) {P : LocPot X}
    (hP : IsPotential A P) : IsPotential B P := by
  refine ⟨fun x => smoothOn_of_compatible h (P.isOpen_U x) (hP.1 x), fun x x' y hy => ?_⟩
  obtain ⟨W, hW, hyW, G, hG, hφ⟩ := hP.2 x x' y hy
  exact ⟨W, hW, hyW, G, holoOn_of_compatible h hW hG, hφ⟩

theorem compatible_unionAtlas_left (A B : FinHolAtlas e X) (h : A.Compatible B) :
    A.Compatible (unionAtlas A B h) := by
  refine ⟨fun j k => ?_, fun j k => ?_⟩
  · induction k using Fin.addCases with
    | left k => simpa using A.holo j k
    | right k => simpa using h.1 j k
  · induction j using Fin.addCases with
    | left j => simpa using A.holo j k
    | right j => simpa using h.2 j k

theorem compatible_unionAtlas_right (A B : FinHolAtlas e X) (h : A.Compatible B) :
    B.Compatible (unionAtlas A B h) := by
  refine ⟨fun j k => ?_, fun j k => ?_⟩
  · induction k using Fin.addCases with
    | left k => simpa using h.2 j k
    | right k => simpa using B.holo j k
  · induction j using Fin.addCases with
    | left j => simpa using h.1 j k
    | right j => simpa using B.holo j k

theorem locDens_unionAtlas_castAdd (A B : FinHolAtlas e X) (h : A.Compatible B)
    (Φ : Fin e → LocPot X) (j : Fin A.n) :
    locDens (unionAtlas A B h) Φ (Fin.castAdd B.n j) = locDens A Φ j := by
  funext y
  simp only [locDens, unionAtlas_chart_castAdd]

theorem locDens_unionAtlas_natAdd (A B : FinHolAtlas e X) (h : A.Compatible B)
    (Φ : Fin e → LocPot X) (k : Fin B.n) :
    locDens (unionAtlas A B h) Φ (Fin.natAdd A.n k) = locDens B Φ k := by
  funext y
  simp only [locDens, unionAtlas_chart_natAdd]

theorem mIntegrable_of_compatible {A B : FinHolAtlas e X} (h : A.Compatible B)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) {g : X → ℝ}
    (hg : MIntegrable A Φ g) : MIntegrable B Φ g := by
  have hΦU : ∀ i, IsPotential (unionAtlas A B h) (Φ i) := fun i =>
    isPotential_of_compatible (compatible_unionAtlas_left A B h) (hΦ i)
  intro k K hK hKc
  refine LocallyIntegrableOn.integrableOn_isCompact (fun y hyK => ?_) hKc
  have hy : y ∈ (B.chart k).target := hK hyK
  obtain ⟨j, hj⟩ := A.cover ((B.chart k).symm y)

  have hVo : IsOpen ((B.chart k).target ∩ (B.chart k).symm ⁻¹' (A.chart j).source) :=
    (B.chart k).isOpen_inter_preimage_symm (A.chart j).open_source
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hVo y ⟨hy, hj⟩
  have hsub : Metric.closedBall y (r / 2) ⊆
      (B.chart k).target ∩ (B.chart k).symm ⁻¹' (A.chart j).source :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  have hbV : Metric.ball y (r / 2) ⊆
      (B.chart k).target ∩ (B.chart k).symm ⁻¹' (A.chart j).source :=
    Metric.ball_subset_closedBall.trans hsub

  have hτa : AnalyticOnNhd ℂ (A.chart j ∘ (B.chart k).symm)
      ((B.chart k).target ∩ (B.chart k).symm ⁻¹' (A.chart j).source) := h.2 k j
  have hinj : Set.InjOn (A.chart j ∘ (B.chart k).symm)
      ((B.chart k).target ∩ (B.chart k).symm ⁻¹' (A.chart j).source) := by
    intro a ha b hb hab
    have h1 : (B.chart k).symm a = (B.chart k).symm b := (A.chart j).injOn ha.2 hb.2 hab
    exact (B.chart k).symm.injOn (by simpa using ha.1) (by simpa using hb.1) h1
  have hmaps : ∀ z ∈ (B.chart k).target ∩ (B.chart k).symm ⁻¹' (A.chart j).source,
      (A.chart j ∘ (B.chart k).symm) z ∈ (A.chart j).target := fun z hz =>
    (A.chart j).map_source hz.2

  have hcpt : IsCompact ((A.chart j ∘ (B.chart k).symm) '' Metric.closedBall y (r / 2)) :=
    (isCompact_closedBall y (r / 2)).image_of_continuousOn (hτa.continuousOn.mono hsub)
  have hA : IntegrableOn (fun w => g ((A.chart j).symm w) * locDens A Φ j w)
      ((A.chart j ∘ (B.chart k).symm) '' Metric.ball y (r / 2)) :=
    (hg j _ (by rintro _ ⟨z, hz, rfl⟩; exact hmaps z (hsub hz)) hcpt).mono_set
      (Set.image_mono Metric.ball_subset_closedBall)
  have hB := (ReciprocityTheory.AnForm.A.integrableOn_image_iff_analytic (A.chart j ∘ (B.chart k).symm)
    (Metric.ball y (r / 2)) Metric.isOpen_ball (hτa.mono hbV) (hinj.mono hbV)
    (fun w => g ((A.chart j).symm w) * locDens A Φ j w)).1 hA
  refine ⟨Metric.ball y (r / 2), mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds y (half_pos hr)),
    hB.congr_fun (fun z hz => ?_) Metric.isOpen_ball.measurableSet⟩
  have hzV := hbV hz
  have key := locDensChart (unionAtlas A B h) Φ hΦU (Fin.natAdd A.n k) (Fin.castAdd B.n j) z
    (by simpa using hzV.1) (by simpa using hzV.2)
  simp only [unionAtlas_chart_natAdd, unionAtlas_chart_castAdd, locDens_unionAtlas_natAdd,
    locDens_unionAtlas_castAdd] at key
  have hleft : (A.chart j).symm (A.chart j ((B.chart k).symm z)) = (B.chart k).symm z :=
    (A.chart j).left_inv hzV.2
  simp only [smul_eq_mul, ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq, key,
    Function.comp_apply, hleft]
  ring

def ChartPartition.extendLeft [CompactSpace X] [T2Space X] {A B : FinHolAtlas e X}
    (h : A.Compatible B) (P : ChartPartition A) : ChartPartition (unionAtlas A B h) where
  χ := Fin.append P.χ (fun _ _ => 0)
  smooth j := by
    induction j using Fin.addCases with
    | left j =>
      show (unionAtlas A B h).SmoothOn Set.univ _
      rw [Fin.append_left]
      exact smoothOn_of_compatible (compatible_unionAtlas_left A B h) isOpen_univ (P.smooth j)
    | right j =>
      intro k
      rw [Fin.append_right]
      exact contDiffOn_const
  nonneg j x := by
    induction j using Fin.addCases with
    | left j => simpa using P.nonneg j x
    | right j => simp
  tsupport_subset j := by
    induction j using Fin.addCases with
    | left j => simpa using P.tsupport_subset j
    | right j =>
      have : (fun _ : X => (0 : ℝ)) = 0 := rfl
      simp [this]
  sum_eq_one x := by
    change ∑ j : Fin (A.n + B.n), Fin.append P.χ (fun _ _ => 0) j x = 1
    rw [Fin.sum_univ_add]
    simpa using P.sum_eq_one x

def ChartPartition.extendRight [CompactSpace X] [T2Space X] {A B : FinHolAtlas e X}
    (h : A.Compatible B) (Q : ChartPartition B) : ChartPartition (unionAtlas A B h) where
  χ := Fin.append (fun _ _ => 0) Q.χ
  smooth j := by
    induction j using Fin.addCases with
    | left j =>
      intro k
      rw [Fin.append_left]
      exact contDiffOn_const
    | right j =>
      show (unionAtlas A B h).SmoothOn Set.univ _
      rw [Fin.append_right]
      exact smoothOn_of_compatible (compatible_unionAtlas_right A B h) isOpen_univ (Q.smooth j)
  nonneg j x := by
    induction j using Fin.addCases with
    | left j => simp
    | right j => simpa using Q.nonneg j x
  tsupport_subset j := by
    induction j using Fin.addCases with
    | left j =>
      have : (fun _ : X => (0 : ℝ)) = 0 := rfl
      simp [this]
    | right j => simpa using Q.tsupport_subset j
  sum_eq_one x := by
    change ∑ j : Fin (A.n + B.n), Fin.append (fun _ _ => 0) Q.χ j x = 1
    rw [Fin.sum_univ_add]
    simpa using Q.sum_eq_one x

theorem integralWith_extendLeft [CompactSpace X] [T2Space X] {A B : FinHolAtlas e X}
    (h : A.Compatible B) (P : ChartPartition A) (Φ : Fin e → LocPot X) (g : X → ℝ) :
    integralWith (unionAtlas A B h) (P.extendLeft h) Φ g = integralWith A P Φ g := by
  unfold integralWith
  show ∑ j : Fin (A.n + B.n), _ = _
  rw [Fin.sum_univ_add]
  simp [ChartPartition.extendLeft, Fin.append_left, Fin.append_right, locDens_unionAtlas_castAdd]

theorem integralWith_extendRight [CompactSpace X] [T2Space X] {A B : FinHolAtlas e X}
    (h : A.Compatible B) (Q : ChartPartition B) (Φ : Fin e → LocPot X) (g : X → ℝ) :
    integralWith (unionAtlas A B h) (Q.extendRight h) Φ g = integralWith B Q Φ g := by
  unfold integralWith
  show ∑ j : Fin (A.n + B.n), _ = _
  rw [Fin.sum_univ_add]
  simp [ChartPartition.extendRight, Fin.append_left, Fin.append_right, locDens_unionAtlas_natAdd]

theorem mIntAtlasIndep : MIntAtlasIndepStatement := by
  intro e X _ _ _ A B h Φ hΦ g hg
  have hgB : MIntegrable B Φ g := mIntegrable_of_compatible h Φ hΦ hg
  refine ⟨hgB, ?_⟩
  have hU : ∀ i, IsPotential (unionAtlas A B h) (Φ i) := fun i =>
    isPotential_of_compatible (compatible_unionAtlas_left A B h) (hΦ i)
  have hgU : MIntegrable (unionAtlas A B h) Φ g :=
    mIntegrable_of_compatible (compatible_unionAtlas_left A B h) Φ hΦ hg
  have hΦB : ∀ i, IsPotential B (Φ i) := fun i => isPotential_of_compatible h (hΦ i)
  obtain ⟨P⟩ := existsPartition A
  obtain ⟨Q⟩ := existsPartition B
  rw [mIntEq A P Φ hΦ g hg, mIntEq B Q Φ hΦB g hgB, ← integralWith_extendLeft h P Φ g,
    ← integralWith_extendRight h Q Φ g]
  exact integralWithIndep _ _ _ Φ hU g hgU

end

end ReciprocityTheory.AnForm.M
