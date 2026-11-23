import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StatementsPullback
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_zero levi_add_smul)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential HoloMap IsDegreeOff mInt MIntegrable)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ThGe ell errE)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe (compat_chart contDiffAt_comp_symm)

noncomputable section

section Maps

variable {D E : ℕ} {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
  {B : FinHolAtlas D Y} {A : FinHolAtlas E Z} {f : Y → Z}

theorem comp_chart_eventuallyEq (hf : HoloMap B A f) (g : Z → ℝ) (j : Fin B.n) (k : Fin A.n)
    {y : Fin D → ℂ} (hy : y ∈ (B.chart j).target)
    (hk : f ((B.chart j).symm y) ∈ (A.chart k).source) :
    (g ∘ f) ∘ (B.chart j).symm =ᶠ[𝓝 y]
      (g ∘ (A.chart k).symm) ∘ (A.chart k ∘ f ∘ (B.chart j).symm) := by
  filter_upwards [ReciprocityTheory.AnForm.M.holoMap_preimage_mem_nhds hf j k hy hk] with z hz
  simp only [Function.comp_apply, (A.chart k).left_inv hz.2]

theorem contDiffAt_comp_map (hf : HoloMap B A f) (g : Z → ℝ) (j : Fin B.n) (k : Fin A.n)
    {y : Fin D → ℂ} (hy : y ∈ (B.chart j).target)
    (hk : f ((B.chart j).symm y) ∈ (A.chart k).source)
    (hg : ContDiffAt ℝ 2 (g ∘ (A.chart k).symm) (A.chart k (f ((B.chart j).symm y)))) :
    ContDiffAt ℝ 2 ((g ∘ f) ∘ (B.chart j).symm) y := by
  have hτ : ContDiffAt ℝ 2 (A.chart k ∘ f ∘ (B.chart j).symm) y :=
    (show AnalyticAt ℝ (A.chart k ∘ f ∘ (B.chart j).symm) y from
      (hf.2 j k y ⟨hy, hk⟩).restrictScalars).contDiffAt
  exact (hg.comp y hτ).congr_of_eventuallyEq (comp_chart_eventuallyEq hf g j k hy hk)

theorem smooth_comp (hf : HoloMap B A f) {g : Z → ℝ} (hg : A.Smooth g) : B.Smooth (g ∘ f) := by
  intro j y hy
  obtain ⟨k, hk⟩ := A.cover (f ((B.chart j).symm y))
  have hτ : ContDiffAt ℝ ∞ (A.chart k ∘ f ∘ (B.chart j).symm) y :=
    (show AnalyticAt ℝ (A.chart k ∘ f ∘ (B.chart j).symm) y from
      (hf.2 j k y ⟨hy.1, hk⟩).restrictScalars).contDiffAt
  have hmem : (A.chart k).target ∩ (A.chart k).symm ⁻¹' Set.univ ∈
      𝓝 ((A.chart k ∘ f ∘ (B.chart j).symm) y) := by
    rw [Set.preimage_univ, Set.inter_univ]
    exact (A.chart k).open_target.mem_nhds ((A.chart k).map_source hk)
  exact (((hg k).contDiffAt hmem).comp y hτ).congr_of_eventuallyEq
    (comp_chart_eventuallyEq hf g j k hy.1 hk) |>.contDiffWithinAt

theorem levi_comp_map (hf : HoloMap B A f) (g : Z → ℝ) (j : Fin B.n) (k : Fin A.n)
    {y : Fin D → ℂ} (hy : y ∈ (B.chart j).target)
    (hk : f ((B.chart j).symm y) ∈ (A.chart k).source)
    (hg : ContDiffAt ℝ 2 (g ∘ (A.chart k).symm) (A.chart k (f ((B.chart j).symm y))))
    (w : Fin D → ℂ) :
    levi ((g ∘ f) ∘ (B.chart j).symm) y w =
      levi (g ∘ (A.chart k).symm) (A.chart k (f ((B.chart j).symm y)))
        (fderiv ℂ (A.chart k ∘ f ∘ (B.chart j).symm) y w) := by
  rw [levi_congr (comp_chart_eventuallyEq hf g j k hy hk) w]
  exact levi_comp w (hf.2 j k y ⟨hy, hk⟩) hg

theorem thGe_pullback {R' : RegChartData B} {R : RegChartData A} (hP : IsPullbackData R' R f)
    {K : ℝ} (hK : ∀ (x x' : Y) (k : Fin B.n),
      ∀ y ∈ (B.chart k).target ∩ (B.chart k).symm ⁻¹' (R'.om.U x ∩ f ⁻¹' R.om.U (f x')),
      ∀ w : Fin D → ℂ, levi ((fun z => R.om.φ (f x') (f z)) ∘ (B.chart k).symm) y w ≤
        K * levi (R'.om.φ x ∘ (B.chart k).symm) y w)
    {g : Z → ℝ} (hg : A.Smooth g) {e e' : ℝ} (hS : ThGe A R.θ g R.om (-e))
    (he : |e| * |K| ≤ e') : ThGe B R'.θ (g ∘ f) R'.om (-e') := by
  intro x k y hy w
  have hyt : y ∈ (B.chart k).target := hy.1
  have hqs : (B.chart k).symm y ∈ (B.chart k).source := (B.chart k).map_target hyt
  have hqy : B.chart k ((B.chart k).symm y) = y := (B.chart k).right_inv hyt
  obtain ⟨k', hk'⟩ := A.cover (f ((B.chart k).symm y))
  have hp' : A.chart k' (f ((B.chart k).symm y)) ∈ (A.chart k').target :=
    (A.chart k').map_source hk'
  have hpp : (A.chart k').symm (A.chart k' (f ((B.chart k).symm y))) = f ((B.chart k).symm y) :=
    (A.chart k').left_inv hk'
  have hθ' : ContDiffAt ℝ 2 (R'.θ.φ x ∘ (B.chart k).symm) y := by
    have h := contDiffAt_comp_symm (R'.θ.isOpen_U x) (R'.θ_pot.1 x) (compat_chart B k) hy.2.1 hqs
    rwa [hqy] at h
  have hgC := contDiffAt_comp_symm isOpen_univ hg (compat_chart A k') trivial hk'
  have hθC := contDiffAt_comp_symm (R.θ.isOpen_U (f ((B.chart k).symm y)))
    (R.θ_pot.1 (f ((B.chart k).symm y))) (compat_chart A k') (R.θ.mem_U _) hk'
  have hωC := contDiffAt_comp_symm (R.om.isOpen_U (f ((B.chart k).symm y)))
    (R.om_pot.1 (f ((B.chart k).symm y))) (compat_chart A k') (R.om.mem_U _) hk'
  have hsumC : ContDiffAt ℝ 2
      ((fun z => R.θ.φ (f ((B.chart k).symm y)) z + g z) ∘ (A.chart k').symm)
      (A.chart k' (f ((B.chart k).symm y))) := hθC.add hgC

  have e1 : levi ((fun z => R'.θ.φ x z + (g ∘ f) z) ∘ (B.chart k).symm) y w =
      levi (R'.θ.φ x ∘ (B.chart k).symm) y w + 1 * levi ((g ∘ f) ∘ (B.chart k).symm) y w := by
    rw [← levi_add_smul 1 hθ' (contDiffAt_comp_map hP.holo g k k' hyt hk' hgC) w]
    exact levi_congr (Eventually.of_forall fun z => by simp [Function.comp]) w
  have e2 : levi (((fun z => R.θ.φ (f ((B.chart k).symm y)) z + g z) ∘ f) ∘ (B.chart k).symm) y w =
      levi ((R.θ.φ (f ((B.chart k).symm y)) ∘ f) ∘ (B.chart k).symm) y w +
        1 * levi ((g ∘ f) ∘ (B.chart k).symm) y w := by
    rw [← levi_add_smul 1 (contDiffAt_comp_map hP.holo _ k k' hyt hk' hθC)
      (contDiffAt_comp_map hP.holo g k k' hyt hk' hgC) w]
    exact levi_congr (Eventually.of_forall fun z => by simp [Function.comp]) w
  have e3 := levi_comp_map hP.holo _ k k' hyt hk' hsumC w
  have e4 : levi (R'.θ.φ x ∘ (B.chart k).symm) y w =
      levi ((R.θ.φ (f ((B.chart k).symm y)) ∘ f) ∘ (B.chart k).symm) y w :=
    hP.θ_eq x ((B.chart k).symm y) k y ⟨hyt, hy.2.1, R.θ.mem_U _⟩ w
  have hbase := hS (f ((B.chart k).symm y)) k' (A.chart k' (f ((B.chart k).symm y)))
    ⟨hp', by rw [Set.mem_preimage, hpp]; exact ⟨R.θ.mem_U _, R.om.mem_U _⟩⟩
    (fderiv ℂ (A.chart k' ∘ f ∘ (B.chart k).symm) y w)
  have e5 := levi_comp_map hP.holo _ k k' hyt hk' hωC w
  have hKy := hK x ((B.chart k).symm y) k y ⟨hyt, hy.2.2, R.om.mem_U _⟩ w
  have hLz : 0 ≤ levi (R.om.φ (f ((B.chart k).symm y)) ∘ (A.chart k').symm)
      (A.chart k' (f ((B.chart k).symm y))) (fderiv ℂ (A.chart k' ∘ f ∘ (B.chart k).symm) y w) := by
    by_cases hv : fderiv ℂ (A.chart k' ∘ f ∘ (B.chart k).symm) y w = 0
    · rw [hv, levi_zero]
    · exact (R.om_pos _ k' _ ⟨hp', by rw [Set.mem_preimage, hpp]; exact R.om.mem_U _⟩ _ hv).le
  have hL' : 0 ≤ levi (R'.om.φ x ∘ (B.chart k).symm) y w := by
    by_cases hw : w = 0
    · rw [hw, levi_zero]
    · exact (R'.om_pos x k y ⟨hyt, hy.2.2⟩ w hw).le
  have hz : levi ((fun z => R.om.φ (f ((B.chart k).symm y)) (f z)) ∘ (B.chart k).symm) y w =
      levi (R.om.φ (f ((B.chart k).symm y)) ∘ (A.chart k').symm)
        (A.chart k' (f ((B.chart k).symm y))) (fderiv ℂ (A.chart k' ∘ f ∘ (B.chart k).symm) y w) :=
    e5
  rw [hz] at hKy
  have h1 := mul_le_mul_of_nonneg_right (le_abs_self e) hLz
  have h2 := mul_le_mul_of_nonneg_left (hKy.trans (mul_le_mul_of_nonneg_right (le_abs_self K) hL'))
    (abs_nonneg e)
  have h3 := mul_le_mul_of_nonneg_right he hL'
  rw [e1, e4, ← e2, e3]
  nlinarith

end Maps

theorem SystemPullback.proof (hc2 : C2ConvergencePullback.Statement) : SystemPullback.Statement := by
  intro D E Y Z _ _ B A R' R f hP S
  obtain ⟨K, hK⟩ := hP.om_le
  have hYo : ∀ y ∈ R'.Yo, f y ∈ R.Yo := fun y hy => by rw [hP.Yo_eq] at hy; exact hy
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = (|K| + 1) * |S.C| := ⟨_, rfl⟩
  have hCC' : |S.C| ≤ C' := by
    rw [hC']; exact le_mul_of_one_le_left (abs_nonneg _) (by linarith [abs_nonneg K])
  have herr : ∀ c t, errE c t = c * (Real.log (ell t) / ell t) := fun c t => by
    unfold errE; ring
  have ha : ∀ t, 1 ≤ ell t → 0 ≤ Real.log (ell t) / ell t := fun t h =>
    div_nonneg (Real.log_nonneg h) (by linarith)
  have hle : ∀ t, 1 ≤ ell t → errE S.C t ≤ errE C' t := fun t h => by
    rw [herr, herr]; exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans hCC') (ha t h)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), A.Smooth (S.ph t) := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (Real.exp_pos (-S.ell₀))] with t ht ht'
    refine S.smooth t ht ?_
    have h1 : Real.log t < -S.ell₀ := by
      have := Real.log_lt_log ht ht'.2
      rwa [Real.log_exp] at this
    show S.ell₀ ≤ Real.log t⁻¹
    rw [Real.log_inv]; linarith
  have hc := hc2 B A f hP.holo R.Yo R.isOpen_Yo S.ph R.φ R'.φ R.φ_smooth
    (fun y hy => hP.φ_eq y (by rw [hP.Yo_eq]; exact hy)) hev S.c2
  refine ⟨{ ph := fun t y => S.ph t (f y)
            C := C'
            ell₀ := max S.ell₀ 1
            smooth := ?_
            le_ph := ?_
            ph_le := ?_
            le_log := ?_
            thGe := ?_
            near := ?_
            far := ?_
            mono := ?_
            c2 := ?_ }, fun _ _ => rfl⟩
  · intro t ht hℓ
    exact smooth_comp hP.holo (S.smooth t ht (le_of_max_le_left hℓ))
  · intro t ht hℓ y hy
    rw [hP.φ_eq y hy]
    exact S.le_ph t ht (le_of_max_le_left hℓ) (f y) (hYo y hy)
  · intro t ht hℓ y
    exact (S.ph_le t ht (le_of_max_le_left hℓ) (f y)).trans ((le_abs_self _).trans hCC')
  · intro t ht hℓ y
    have hl : 0 ≤ Real.log (ell t) := Real.log_nonneg (le_of_max_le_right hℓ)
    have h1 := S.le_log t ht (le_of_max_le_left hℓ) (f y)
    have h2 := mul_le_mul_of_nonneg_right ((le_abs_self S.C).trans hCC') hl
    linarith
  · intro t ht hℓ
    refine thGe_pullback hP hK (S.smooth t ht (le_of_max_le_left hℓ))
      (S.thGe t ht (le_of_max_le_left hℓ)) ?_
    have h0 := ha t (le_of_max_le_right hℓ)
    rw [herr, herr, abs_mul, abs_of_nonneg h0, hC']
    nlinarith [mul_nonneg (abs_nonneg S.C) h0, abs_nonneg K]
  · intro t ht hℓ y hy hr
    rw [hP.r_eq y hy] at hr
    rw [hP.φ_eq y hy]
    have h1 := S.near t ht (le_of_max_le_left hℓ) (f y) (hYo y hy) hr
    have h2 := hle t (le_of_max_le_right hℓ)
    linarith
  · intro t ht hℓ y hy
    rw [hP.φ_eq y hy, hP.r_eq y hy]
    have h1 := S.far t ht (le_of_max_le_left hℓ) (f y) (hYo y hy)
    have hr : 0 ≤ R.r (f y) := by linarith [R.one_le_r (f y) (hYo y hy)]
    have h2 := mul_le_mul_of_nonneg_right (hle t (le_of_max_le_right hℓ)) hr
    linarith
  · intro t t₀ ht htt hℓ y
    have h1 : 1 ≤ ell t₀ := le_of_max_le_right hℓ
    have h0 := ha t₀ h1
    have hm := S.mono t t₀ ht htt (le_of_max_le_left hℓ) (f y)
    have hsq : S.C * S.C ≤ C' * C' := by
      have := mul_self_le_mul_self (abs_nonneg S.C) hCC'
      rwa [abs_mul_abs_self] at this
    have h2 := mul_le_mul_of_nonneg_right hsq h0
    rw [herr] at hm
    rw [herr]
    nlinarith
  · intro k K' hK' hKs
    rw [hP.Yo_eq] at hKs
    exact hc k K' hK' hKs

section Cover

variable {D : ℕ} {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] [CompactSpace Y]
  [T2Space Y] [CompactSpace Z] [T2Space Z] {B : FinHolAtlas D Y} {A : FinHolAtlas D Z} {h : Y → Z}

end Cover

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
