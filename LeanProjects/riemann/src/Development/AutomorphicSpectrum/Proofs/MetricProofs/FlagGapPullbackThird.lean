import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumSqCompBlockMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsPermOfRange
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HoloOnDivCongr
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AevalNeZeroOfNotMem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPointsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMetricExplicitMatrixFormStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogBlockMetricOffBoundaryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMetricGrassmannChartLocalStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMetricRowEchelonLocalStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapPullbackFirstStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.ChartEx

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

section Holo

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {W W' : Set X} {f g : X → ℂ}

theorem holo_mono (h : A.HoloOn W f) (s : W' ⊆ W) : A.HoloOn W' f := fun j =>
  (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono s))

theorem holo_const (c : ℂ) : A.HoloOn W fun _ => c := fun _ => analyticOnNhd_const

theorem holo_add (hf : A.HoloOn W f) (hg : A.HoloOn W g) : A.HoloOn W fun t => f t + g t :=
  fun j => (hf j).add (hg j)

theorem holo_mul (hf : A.HoloOn W f) (hg : A.HoloOn W g) : A.HoloOn W fun t => f t * g t :=
  fun j => (hf j).mul (hg j)

theorem holo_div (hf : A.HoloOn W f) (hg : A.HoloOn W g) (h0 : ∀ t ∈ W, g t ≠ 0) :
    A.HoloOn W fun t => f t / g t :=
  fun j => (hf j).div (hg j) fun _ hy => h0 _ hy.2

theorem holo_zpow (n : ℤ) (hf : A.HoloOn W f) (h0 : ∀ t ∈ W, f t ≠ 0) : A.HoloOn W fun t => f t ^ n :=
  fun j y hy => AnalyticAt.zpow (hf j y hy) (h0 _ hy.2)

theorem holo_sum {T : Type} (s : Finset T) {F : T → X → ℂ} (h : ∀ a ∈ s, A.HoloOn W (F a)) :
    A.HoloOn W fun t => ∑ a ∈ s, F a t := by
  induction s using Finset.induction_on with
  | empty => simpa using holo_const (A := A) (W := W) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact holo_add (h a (Finset.mem_insert_self _ _)) (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem holo_prod {T : Type} (s : Finset T) {F : T → X → ℂ} (h : ∀ a ∈ s, A.HoloOn W (F a)) :
    A.HoloOn W fun t => ∏ a ∈ s, F a t := by
  induction s using Finset.induction_on with
  | empty => simpa using holo_const (A := A) (W := W) 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact holo_mul (h a (Finset.mem_insert_self _ _)) (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem holo_continuousOn (hW : IsOpen W) (h : A.HoloOn W f) : ContinuousOn f W := by
  intro t ht
  obtain ⟨j, hj⟩ := A.cover t
  have h1 : AnalyticAt ℂ (f ∘ (A.chart j).symm) (A.chart j t) :=
    h j _ ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using ht⟩
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) t :=
    ContinuousAt.comp h1.continuousAt ((A.chart j).continuousAt hj)
  have h3 : ((f ∘ (A.chart j).symm) ∘ A.chart j) =ᶠ[𝓝 t] f := by
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with u hu
    simp [(A.chart j).left_inv hu]
  exact (h2.congr h3).continuousWithinAt

end Holo

section Main

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {M : FlagModel y Ψ N j} {n : ℕ}
  {BM : BaseMetric M n} {p : Ψ × Fin N} {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]
  {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} {e : ℕ} {R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e}
  {pr : R.X → BM.Rb.X}

def zc (v : (Σ k, ιk k) → (Σ k, ι k)) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (x t : R.X) : (Σ k, ι k) → ℂ :=
  Function.extend v (R.lift x t) fun _ => 1

theorem zc_holo (hb : IsBlockMap κ v) (x : R.X) (q : Σ k, ι k) : R.A.HoloOn (R.U x) fun t => zc v R x t q := by
  by_cases h : ∃ a, v a = q
  · obtain ⟨a, rfl⟩ := h
    have : (fun t => zc v R x t (v a)) = fun t => R.lift x t a :=
      funext fun t => hb.2.1.extend_apply _ _ _
    rw [this]
    exact R.holo x a
  · have : (fun t => zc v R x t q) = fun _ => 1 := funext fun t => Function.extend_apply' _ _ _ h
    rw [this]
    exact holo_const 1

theorem exists_pt (hyp : IsStepHyp M BM p κ v R pr) (x t : R.X) (ht : t ∈ R.U x) :
    ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x t ∧
      SameOrbit (basePart M.blk z) (BM.Rb.lift (pr t) (pr t)) := by
  obtain ⟨hb, -, -, hl⟩ := hyp
  obtain ⟨z₀, hz₀, hv, c₀, hc₀, hcb⟩ := hl t
  obtain ⟨c, hc, hcl⟩ := R.compat x t t ⟨ht, R.mem_U t⟩
  let c' : K → ℂ := Function.extend κ c fun _ => 1
  have hcκ : ∀ a, c' (κ a) = c a := fun a => hb.1.extend_apply _ _ _
  have hc' : ∀ k, c' k ≠ 0 := fun k => by
    by_cases h : ∃ a, κ a = k
    · obtain ⟨a, rfl⟩ := h
      rw [hcκ]; exact hc a
    · have : c' k = 1 := Function.extend_apply' _ _ _ h
      rw [this]; exact one_ne_zero
  have T := (TorusAct.main K ι Φ y z₀ c' hc').2 hz₀
  refine ⟨fun q => c' q.1 * z₀ q, T.1, ?_, ?_⟩
  · funext q
    show c' (v q).1 * z₀ (v q) = R.lift x t q
    rw [hb.2.2.1 q, hcκ, hcl]
    show c q.1 * z₀ (v q) = c q.1 * R.lift t t q
    rw [← hv]; rfl
  · refine ⟨fun k => c' k.1 * c₀ k, fun k => mul_ne_zero (hc' _) (hc₀ _), ?_⟩
    funext q
    have h1 := congrFun hcb q
    show c' q.1.1 * basePart M.blk z₀ q = c' q.1.1 * c₀ q.1 * _
    rw [h1, mul_assoc]

theorem zc_eq (hb : IsBlockMap κ v) {x t : R.X} {z : (Σ k, ι k) → ℂ} (hz : z ∘ v = R.lift x t) {k : K}
    (hk : k ∈ Set.range κ) (i : ι k) : zc v R x t ⟨k, i⟩ = z ⟨k, i⟩ := by
  obtain ⟨q, hq⟩ := hb.2.2.2 ⟨k, i⟩ hk
  rw [← hq]
  show Function.extend v (R.lift x t) _ (v q) = _
  rw [hb.2.1.extend_apply, ← hz]
  rfl

theorem base_eq (hyp : IsStepHyp M BM p κ v R pr) {x t : R.X} {z : (Σ k, ι k) → ℂ} (hz : z ∘ v = R.lift x t) :
    basePart M.blk (zc v R x t) = basePart M.blk z :=
  funext fun q => zc_eq hyp.1 hz (hyp.2.1 _ (Or.inl q.1.2)) q.2

theorem baseMono_eq (F : FrameData ι Ψ N M.Ω M.blk) {z z' : (Σ k, ι k) → ℂ}
    (h : basePart M.blk z = basePart M.blk z') : baseMono M F p z = baseMono M F p z' := by
  unfold baseMono; rw [h]

theorem plk_eq (hyp : IsStepHyp M BM p κ v R pr) (F : FrameData ι Ψ N M.Ω M.blk) {k₀ : K}
    (hk : M.blk p = some k₀) {x t : R.X} {z : (Σ k, ι k) → ℂ} (hz : z ∘ v = R.lift x t) :
    plk M F k₀ (zc v R x t) = plk M F k₀ z := by
  funext I
  unfold plk
  rw [base_eq hyp hz]
  exact Finset.sum_congr rfl fun m _ => by rw [zc_eq hyp.1 hz (hyp.2.1 _ (Or.inr hk)) m]

theorem base_mem (hyp : IsStepHyp M BM p κ v R pr) {x t : R.X} (ht : t ∈ R.U x) :
    basePart M.blk (zc v R x t) ∈ mcPts (mCoordIdeal M.x) := by
  obtain ⟨z, hz, hv, -⟩ := exists_pt hyp x t ht
  rw [base_eq hyp hv]
  exact (GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M).1 z hz

theorem good_at (hyp : IsStepHyp M BM p κ v R pr) {x t : R.X} (ht : t ∈ R.U x) {l : Fin BM.q}
    (hl : pr t ∈ BM.O l) : M.GoodAt (BM.F l) (mCoordIdeal (basePart M.blk (zc v R x t))) := by
  obtain ⟨z, -, hv, c, hc, hcb⟩ := exists_pt hyp x t ht
  rw [base_eq hyp hv, hcb, (TorusAct.main _ _ M.Ω M.x _ c hc).1]
  exact BM.good l _ hl

theorem chart_ne {F : FrameData ι Ψ N M.Ω M.blk} {b : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hG : M.GoodAt F (mCoordIdeal b)) (k : NonPluckerBlocks M.blk) : b ⟨k, F.c k⟩ ≠ 0 := fun h => hG.1 k (by
  show mConeMap b (X ⟨k, F.c k⟩) = 0
  rw [mConeMap, aeval_X, h, map_zero, zero_mul])

theorem dy_range (hyp : IsStepHyp M BM p κ v R pr) (k : K) (h : M.dy p k ≠ 0) : k ∈ Set.range κ := by
  by_cases hk : ∀ p', M.blk p' ≠ some k
  · exact hyp.2.1 k (Or.inl hk)
  · by_cases hp : M.blk p = some k
    · exact hyp.2.1 k (Or.inr hp)
    · exact (h ((dif_neg hk).trans (if_neg hp))).elim

theorem log_side (hyp : IsStepHyp M BM p κ v R pr) {x t : R.X} (ht : t ∈ R.U x) (hbd : pr t ∉ bdry BM.s)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (hv : z ∘ v = R.lift x t) :
    Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h (R.lift x t)) + stepPh M BM p v R pr t =
      Real.log ((BM.hom p).h z) := by
  rw [GlobalTheory.T.flag_gap_pullback_first K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hyp x t z ht hbd hz hv, ← hv,
    ← fsHerm_h_blockMap K ι Kk ιk κ v (M.dy p) z hyp.1 (dy_range hyp), stepGap]
  ring

theorem dom_open (hyp : IsStepHyp M BM p κ v R pr) (x : R.X) (l : Fin BM.q) :
    IsOpen (R.U x ∩ pr ⁻¹' BM.O l) :=
  (R.isOpen_U x).inter ((BM.O_open l).preimage hyp.2.2.1.1)

theorem val_nhd (hyp : IsStepHyp M BM p κ v R pr) (x y₀ : R.X) (l : Fin BM.q)
    (h₀ : y₀ ∈ R.U x ∩ pr ⁻¹' BM.O l) (s : M.Ω)
    (hs : RegAt M.x (mCoordIdeal (basePart M.blk (zc v R x y₀))) s) :
    ∃ W' : Set R.X, IsOpen W' ∧ y₀ ∈ W' ∧ W' ⊆ R.U x ∩ pr ⁻¹' BM.O l ∧
      R.A.HoloOn W' fun t => valAt M.x s (basePart M.blk (zc v R x t)) :=
  ValHolo.holoOn_valAt _ _ M.Ω M.x s e R.X R.A _ (fun t => basePart M.blk (zc v R x t)) y₀ (dom_open hyp x l) h₀
    (fun q => holo_mono (zc_holo hyp.1 x ⟨q.1.1, q.2⟩) Set.inter_subset_left)
    (fun _ ht => base_mem hyp ht.1) hs

theorem baseMono_holo (hyp : IsStepHyp M BM p κ v R pr) (x : R.X) (l : Fin BM.q) :
    R.A.HoloOn (R.U x ∩ pr ⁻¹' BM.O l) fun t => baseMono M (BM.F l) p (zc v R x t) := by
  unfold baseMono
  refine holo_prod _ fun k _ => holo_zpow _ ?_ fun t ht => chart_ne (good_at hyp ht.1 ht.2) k
  exact holo_mono (zc_holo hyp.1 x ⟨k.1, (BM.F l).c k⟩) Set.inter_subset_left

theorem baseMono_ne (hyp : IsStepHyp M BM p κ v R pr) {x t : R.X} {l : Fin BM.q}
    (ht : t ∈ R.U x ∩ pr ⁻¹' BM.O l) : baseMono M (BM.F l) p (zc v R x t) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (chart_ne (good_at hyp ht.1 ht.2) k)

theorem chart_none (hyp : IsStepHyp M BM p κ v R pr) (x y₀ : R.X) (hy₀ : y₀ ∈ R.U x) (hp : M.blk p = none)
    (l : Fin BM.q) (hl : pr y₀ ∈ BM.O l) : ∃ W H D, IsStepChart M BM p κ v R pr x y₀ W l H D := by
  have hG₀ := good_at hyp hy₀ hl
  obtain ⟨W, hW, hy, hsub, hval⟩ := val_nhd hyp x y₀ l ⟨hy₀, hl⟩ ((BM.F l).υ p)⁻¹ (hG₀.2.2 p hp).2.2
  refine ⟨W, fun _ => 1, fun t => baseMono M (BM.F l) p (zc v R x t) *
    valAt M.x ((BM.F l).υ p)⁻¹ (basePart M.blk (zc v R x t)), hW, hy, fun t ht => (hsub ht).1,
    fun t ht => (hsub ht).2, fun a b => holo_const _, fun t _ => ⟨isBlockDiag_one, by simp⟩,
    holo_mul (holo_mono (baseMono_holo hyp x l) hsub) hval, fun t ht => ?_, fun t ht hbd => ?_⟩
  · refine mul_ne_zero (baseMono_ne hyp (hsub ht)) fun h0 => ?_
    have hmem := base_mem hyp (hsub ht).1
    have hg := ((good_at hyp (hsub ht).1 (hsub ht).2).2.2 p hp)
    have hr := ValRing.regAt_valAt_ring _ _ M.Ω M.x _ hmem
    have h1 := (hr.2.2.2.2 _ _ hg.2.1 hg.2.2).2.2.1
    rw [mul_inv_cancel₀ hg.1, hr.2.2.2.1, h0, mul_zero] at h1
    exact one_ne_zero h1
  · obtain ⟨z, hz, hv, ho⟩ := exists_pt hyp x t (hsub ht).1
    rw [log_side hyp (hsub ht).1 hbd hz hv,
      GlobalTheory.T.log_block_metric_off_boundary K ι Φ y Ψ N j M n BM p l (pr t) z hp ⟨(hsub ht).2, hbd⟩ hz ho]
    show _ = blockPot j p.2 (BM.G l p.1 (pr t)) 1 + Real.log ‖baseMono M (BM.F l) p (zc v R x t) *
      valAt M.x ((BM.F l).υ p)⁻¹ (basePart M.blk (zc v R x t))‖
    rw [base_eq hyp hv, baseMono_eq (BM.F l) (base_eq hyp hv)]

theorem chart_some (hyp : IsStepHyp M BM p κ v R pr) (x y₀ : R.X) (hy₀ : y₀ ∈ R.U x) {k₀ : K}
    (hp : M.blk p = some k₀) (l : Fin BM.q) (hl : pr y₀ ∈ BM.O l) :
    ∃ W H D, IsStepChart M BM p κ v R pr x y₀ W l H D := by
  have hG₀ := good_at hyp hy₀ hl
  have h1 : ∀ q : Finset (Fin N) × ι k₀, ∃ W' : Set R.X, IsOpen W' ∧ y₀ ∈ W' ∧ W' ⊆ R.U x ∩ pr ⁻¹' BM.O l ∧
      R.A.HoloOn W' fun t => valAt M.x ((BM.F l).u' q.1 ⟨k₀, q.2⟩) (basePart M.blk (zc v R x t)) :=
    fun q => val_nhd hyp x y₀ l ⟨hy₀, hl⟩ _ (hG₀.2.1 _ _).2
  choose Wq hWq hyq hsq hvq using h1
  let W₁ : Set R.X := (R.U x ∩ pr ⁻¹' BM.O l) ∩ ⋂ q, Wq q
  have hW₁ : IsOpen W₁ := (dom_open hyp x l).inter (isOpen_iInter_of_finite hWq)
  have hs₁ : W₁ ⊆ R.U x ∩ pr ⁻¹' BM.O l := Set.inter_subset_left
  let w : R.X → Finset (Fin N) → ℂ := fun t => plk M (BM.F l) k₀ (zc v R x t)
  have hw : ∀ I, R.A.HoloOn W₁ fun t => w t I := fun I => by
    refine holo_sum _ fun m _ => holo_mul ?_ ?_
    · exact holo_mono (hvq (I, m)) fun t ht => Set.mem_iInter.1 ht.2 (I, m)
    · exact holo_mono (zc_holo hyp.1 x _) fun t ht => (hs₁ ht).1
  obtain ⟨z₀, hz₀, hv₀, ho₀⟩ := exists_pt hyp x y₀ hy₀
  obtain ⟨I₀, hI₀, hne₀⟩ := GlobalTheory.T.block_metric_row_echelon_local K ι Φ y Ψ N j M n BM p k₀ l (pr y₀) z₀ hp hl hz₀ ho₀
  rw [← plk_eq hyp _ hp hv₀] at hne₀
  obtain ⟨C, B, hCB⟩ := GrChart.exists_isGrChart N j p.2 I₀ M.j_le hI₀
  let W : Set R.X := W₁ ∩ (fun t => w t I₀) ⁻¹' {0}ᶜ
  have hW : IsOpen W := (holo_continuousOn hW₁ (hw I₀)).isOpen_inter_preimage hW₁ isOpen_compl_singleton
  have hs : W ⊆ W₁ := Set.inter_subset_left
  have hne : ∀ t ∈ W, w t I₀ ≠ 0 := fun t ht => ht.2
  have hy : y₀ ∈ W := ⟨⟨⟨hy₀, hl⟩, Set.mem_iInter.2 hyq⟩, hne₀⟩
  refine ⟨W, fun t => grMat C B I₀ (w t), fun t => baseMono M (BM.F l) p (zc v R x t) * w t I₀, hW, hy,
    fun t ht => (hs₁ (hs ht)).1, fun t ht => (hs₁ (hs ht)).2, fun a b => ?_, fun t ht => ?_,
    holo_mul (holo_mono (baseMono_holo hyp x l) (hs.trans hs₁)) (holo_mono (hw I₀) hs),
    fun t ht => mul_ne_zero (baseMono_ne hyp (hs₁ (hs ht))) (hne t ht), fun t ht hbd => ?_⟩
  · have : (fun t => grMat C B I₀ (w t) a b) = fun t => C a b + ∑ I, w t I / w t I₀ * B I a b := by
      funext t
      simp [grMat, Matrix.add_apply, Matrix.sum_apply]
    rw [this]
    refine holo_add (holo_const _) (holo_sum _ fun I _ => holo_mul ?_ (holo_const _))
    exact holo_div (holo_mono (hw I) hs) (holo_mono (hw I₀) hs) hne
  · obtain ⟨z, hz, hv, ho⟩ := exists_pt hyp x t (hs₁ (hs ht)).1
    obtain ⟨h, a, hh, hd, ha, hw', -⟩ := GlobalTheory.T.block_metric_grassmann_chart_local K ι Φ y Ψ N j M n BM p k₀ l (pr t) z hp (hs₁ (hs ht)).2 hz ho
    have e := plk_eq hyp (BM.F l) hp hv
    have := hCB h a (w t) hh hd ha (fun I hI => by rw [← hw' I hI]; exact congrFun e I) (hne t ht)
    exact ⟨this.1, this.2.1⟩
  · obtain ⟨z, hz, hv, ho⟩ := exists_pt hyp x t (hs₁ (hs ht)).1
    have e := plk_eq hyp (BM.F l) hp hv
    have hnz : plk M (BM.F l) k₀ z I₀ ≠ 0 := by rw [← e]; exact hne t ht
    rw [log_side hyp (hs₁ (hs ht)).1 hbd hz hv,
      GlobalTheory.T.block_metric_explicit_matrix_form K ι Φ y Ψ N j M n BM p k₀ l (pr t) z I₀ C B hp hCB ⟨(hs₁ (hs ht)).2, hbd⟩ hz ho hnz]
    simp only [w]
    rw [e, baseMono_eq (BM.F l) (base_eq hyp hv)]

theorem hasStepCharts (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ)
    (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)]
    (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e)
    (pr : R.X → BM.Rb.X) : IsStepHyp M BM p κ v R pr → HasStepCharts M BM p κ v R pr := by
  intro hyp x y₀ hy₀
  obtain ⟨l, hl⟩ := BM.O_cover (pr y₀)
  rcases hp : M.blk p with _ | k₀
  · obtain ⟨W, H, D, h⟩ := chart_none hyp x y₀ hy₀ hp l hl
    exact ⟨W, l, H, D, h⟩
  · obtain ⟨W, H, D, h⟩ := chart_some hyp x y₀ hy₀ hp l hl
    exact ⟨W, l, H, D, h⟩

end Main

end GlobalTheory.CompanionTheory.Ar.PB.StepW.ChartEx
