import ReciprocityTheory.AnalyticForms.LeviForms.RegChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshRegMax
import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShift
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential

namespace ReciprocityTheory.AnForm.P

open MeasureTheory Metric ReciprocityTheory.AnForm.M FinHolAtlas
open scoped ContDiff

noncomputable section

def chartBall {e : ℕ} {X : Type} [TopologicalSpace X] (B : FinHolAtlas e X) (j : Fin B.n) (ρ : ℝ) :
    Set X :=
  (B.chart j).source ∩ B.chart j ⁻¹' ball 0 ρ

def RegMaxDominatedStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] [DecidableEq ι] (η : ℝ) (t : ι → ℝ) (k₀ : ι)
    (I : Finset ι), 0 < η → k₀ ∈ I → (∀ j ∉ I, t j + η ≤ t k₀) →
      ReciprocityTheory.AnForm.A.regMax η t =
        ReciprocityTheory.AnForm.A.regMax η (fun j => if j ∈ I then t j else t k₀ - η)

private theorem kθ_eq_zero_of_half_le_abs {x : ℝ} (hx : 1 / 2 ≤ |x|) : ReciprocityTheory.AnForm.A.kθ x = 0 := by
  unfold ReciprocityTheory.AnForm.A.kθ
  by_contra hne
  have hm : x ∈ Function.support
      ((⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : ℝ)).normed volume) := hne
  rw [ContDiffBump.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hm
  exact absurd hm (not_lt.mpr hx)

private theorem tmax_eq_of_eqOn_of_le_at_mem {ι : Type} [Fintype ι] [Nonempty ι] (f g : ι → ℝ) (I : Finset ι) (k₀ : ι)
    (hk₀ : k₀ ∈ I) (hI : ∀ j ∈ I, f j = g j) (hf : ∀ j ∉ I, f j ≤ f k₀) (hg : ∀ j ∉ I, g j ≤ g k₀) :
    ReciprocityTheory.AnForm.A.tmax f = ReciprocityTheory.AnForm.A.tmax g := by
  unfold ReciprocityTheory.AnForm.A.tmax
  apply le_antisymm
  · apply Finset.sup'_le
    intro j _
    by_cases hj : j ∈ I
    · rw [hI j hj]
      exact Finset.le_sup' g (Finset.mem_univ j)
    · calc f j ≤ f k₀ := hf j hj
        _ = g k₀ := hI k₀ hk₀
        _ ≤ _ := Finset.le_sup' g (Finset.mem_univ k₀)
  · apply Finset.sup'_le
    intro j _
    by_cases hj : j ∈ I
    · rw [← hI j hj]
      exact Finset.le_sup' f (Finset.mem_univ j)
    · calc g j ≤ g k₀ := hg j hj
        _ = f k₀ := (hI k₀ hk₀).symm
        _ ≤ _ := Finset.le_sup' f (Finset.mem_univ k₀)

theorem regMax_dominated : RegMaxDominatedStatement := by
  intro ι _ _ _ η t k₀ I hη hk₀ hI
  unfold ReciprocityTheory.AnForm.A.regMax
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  dsimp only
  by_cases hs : ∀ j, |h j| < 1 / 2
  · congr 1
    apply tmax_eq_of_eqOn_of_le_at_mem _ _ I k₀ hk₀
    · intro j hj
      simp [hj]
    · intro j hj
      show t j + η * h j ≤ t k₀ + η * h k₀
      have a := mul_lt_mul_of_pos_left (abs_lt.mp (hs j)).2 hη
      have b := mul_lt_mul_of_pos_left (abs_lt.mp (hs k₀)).1 hη
      have c := hI j hj
      linarith
    · intro j hj
      show (if j ∈ I then t j else t k₀ - η) + η * h j ≤ (if k₀ ∈ I then t k₀ else t k₀ - η) + η * h k₀
      rw [if_neg hj, if_pos hk₀]
      have a := mul_lt_mul_of_pos_left (abs_lt.mp (hs j)).2 hη
      have b := mul_lt_mul_of_pos_left (abs_lt.mp (hs k₀)).1 hη
      linarith
  · push_neg at hs
    obtain ⟨j, hj⟩ := hs
    have h0 : ∏ i, ReciprocityTheory.AnForm.A.kθ (h i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (kθ_eq_zero_of_half_le_abs hj)
    rw [h0, mul_zero, mul_zero]

def GlueCutoffStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] (A B : FinHolAtlas e X), A.Compatible B →
    (∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target) →
    ∃ η : Fin B.n → X → ℝ, ∀ j, A.Smooth (η j) ∧ (∀ y, -1 ≤ η j y ∧ η j y ≤ 0) ∧
      (∀ y ∈ chartBall B j 1, η j y = 0) ∧ ∀ y ∉ chartBall B j (9 / 8), η j y = -1

def cutψ (s : ℝ) : ℝ := Real.smoothTransition (64 * (s - 1) / 17)

def cutP {e : ℕ} (z : Fin e → ℂ) : ℝ := ∏ i, (1 - cutψ (‖z i‖ ^ 2))

open Classical in

def glueCut {e : ℕ} {X : Type} [TopologicalSpace X] (B : FinHolAtlas e X) (j : Fin B.n) (y : X) :
    ℝ :=
  if y ∈ (B.chart j).source then cutP (B.chart j y) - 1 else -1

lemma cutψ_nonneg (s : ℝ) : 0 ≤ cutψ s := Real.smoothTransition.nonneg _
lemma cutψ_le_one (s : ℝ) : cutψ s ≤ 1 := Real.smoothTransition.le_one _

lemma cutψ_of_le {s : ℝ} (hs : s ≤ 1) : cutψ s = 0 := by
  unfold cutψ
  apply Real.smoothTransition.zero_of_nonpos
  have h1 : 64 * (s - 1) ≤ 0 := by linarith
  exact div_nonpos_of_nonpos_of_nonneg h1 (by norm_num)

lemma cutψ_of_ge {s : ℝ} (hs : 81 / 64 ≤ s) : cutψ s = 1 := by
  unfold cutψ
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by norm_num)]
  linarith

lemma polydiscCutoff_nonneg {e : ℕ} (z : Fin e → ℂ) : 0 ≤ cutP z := by
  unfold cutP
  exact Finset.prod_nonneg fun i _ => sub_nonneg.mpr (cutψ_le_one _)

lemma cutP_le_one {e : ℕ} (z : Fin e → ℂ) : cutP z ≤ 1 := by
  unfold cutP
  exact Finset.prod_le_one (fun i _ => sub_nonneg.mpr (cutψ_le_one _))
    (fun i _ => by linarith [cutψ_nonneg (‖z i‖ ^ 2)])

lemma polydiscCutoff_eq_one_of_mem_ball {e : ℕ} {z : Fin e → ℂ} (hz : z ∈ ball (0 : Fin e → ℂ) 1) : cutP z = 1 := by
  unfold cutP
  apply Finset.prod_eq_one
  intro i _
  have h1 : ‖z i‖ < 1 := lt_of_le_of_lt (norm_le_pi_norm z i) (mem_ball_zero_iff.mp hz)
  have h2 : ‖z i‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (z i)]
  rw [cutψ_of_le h2, sub_zero]

lemma polydiscCutoff_eq_zero_of_not_mem_ball {e : ℕ} {z : Fin e → ℂ} (hz : z ∉ ball (0 : Fin e → ℂ) (9 / 8)) :
    cutP z = 0 := by
  unfold cutP
  rw [mem_ball_zero_iff, not_lt] at hz
  obtain ⟨i, hi⟩ : ∃ i, 9 / 8 ≤ ‖z i‖ := by
    by_contra hcon
    push_neg at hcon
    have h3 : ‖z‖ < 9 / 8 := (pi_norm_lt_iff (by norm_num)).mpr hcon
    linarith
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have h2 : 81 / 64 ≤ ‖z i‖ ^ 2 := by nlinarith
  rw [cutψ_of_ge h2, sub_self]

lemma cutP_contDiff {e : ℕ} : ContDiff ℝ ∞ (cutP (e := e)) := by
  have hq : ∀ i : Fin e, ContDiff ℝ ∞ (fun z : Fin e → ℂ => 64 * (‖z i‖ ^ 2 - 1) / 17) := fun i =>
    (contDiff_const.mul (((contDiff_apply ℝ ℂ i).norm_sq ℝ).sub contDiff_const)).div_const 17
  unfold cutP cutψ
  exact contDiff_prod fun i _ => contDiff_const.sub (Real.smoothTransition.contDiff.comp (hq i))

private theorem smooth_glueCut_of_compatible {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X]
    (A B : FinHolAtlas e X) (hAB : A.Compatible B)
    (h2 : ∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target) (j : Fin B.n) :
    A.Smooth (glueCut B j) := by
  have hCt : closedBall (0 : Fin e → ℂ) (9 / 8) ⊆ (B.chart j).target :=
    (closedBall_subset_closedBall (by norm_num)).trans (h2 j)
  have hCc : IsClosed ((B.chart j).symm '' closedBall (0 : Fin e → ℂ) (9 / 8)) :=
    ((isCompact_closedBall _ _).image_of_continuousOn
      ((B.chart j).continuousOn_symm.mono hCt)).isClosed
  have hCsrc : (B.chart j).symm '' closedBall (0 : Fin e → ℂ) (9 / 8) ⊆ (B.chart j).source := by
    rintro _ ⟨z, hz, rfl⟩
    exact (B.chart j).map_target (hCt hz)
  have hout : ∀ y, y ∉ (B.chart j).symm '' closedBall (0 : Fin e → ℂ) (9 / 8) →
      glueCut B j y = -1 := by
    intro y hy
    unfold glueCut
    split_ifs with hys
    · have hn : B.chart j y ∉ ball (0 : Fin e → ℂ) (9 / 8) := fun hb =>
        hy ⟨B.chart j y, ball_subset_closedBall hb, (B.chart j).left_inv hys⟩
      rw [polydiscCutoff_eq_zero_of_not_mem_ball hn]
      ring
    · rfl
  intro k
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  by_cases hxs : (A.chart k).symm x ∈ (B.chart j).source
  · refine ⟨(A.chart k).target ∩ (A.chart k).symm ⁻¹' (B.chart j).source,
      (A.chart k).isOpen_inter_preimage_symm (B.chart j).open_source, ⟨hx.1, hxs⟩, ?_⟩
    have hR : ContDiffOn ℝ ∞ (B.chart j ∘ (A.chart k).symm)
        ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (B.chart j).source) :=
      ((hAB.1 k j).contDiffOn (n := ∞) ((A.chart k).isOpen_inter_preimage_symm
        (B.chart j).open_source).uniqueDiffOn).restrict_scalars ℝ
    have hc := (cutP_contDiff.comp_contDiffOn hR).sub (contDiffOn_const (c := (1 : ℝ)))
    refine (hc.mono Set.inter_subset_right).congr ?_
    intro z hz
    show glueCut B j ((A.chart k).symm z) = cutP (B.chart j ((A.chart k).symm z)) - 1
    unfold glueCut
    exact if_pos hz.2.2
  · refine ⟨(A.chart k).target ∩ (A.chart k).symm ⁻¹' ((B.chart j).symm '' closedBall 0 (9 / 8))ᶜ,
      (A.chart k).isOpen_inter_preimage_symm hCc.isOpen_compl, ⟨hx.1, fun hc => hxs (hCsrc hc)⟩, ?_⟩
    refine (contDiffOn_const (c := (-1 : ℝ))).congr ?_
    intro z hz
    exact hout _ hz.2.2

theorem glue_cutoff : GlueCutoffStatement := by
  intro e X _ _ A B hAB h2
  refine ⟨glueCut B, fun j => ⟨smooth_glueCut_of_compatible A B hAB h2 j, fun y => ?_, fun y hy => ?_,
    fun y hy => ?_⟩⟩
  · unfold glueCut
    split_ifs
    · constructor <;> linarith [polydiscCutoff_nonneg (B.chart j y), cutP_le_one (B.chart j y)]
    · norm_num
  · unfold glueCut
    rw [if_pos hy.1, polydiscCutoff_eq_one_of_mem_ball hy.2, sub_self]
  · unfold glueCut
    split_ifs with hys
    · have hn : B.chart j y ∉ ball (0 : Fin e → ℂ) (9 / 8) := fun hb =>
        hy (show y ∈ (B.chart j).source ∩ B.chart j ⁻¹' ball 0 (9 / 8) from ⟨hys, hb⟩)
      rw [polydiscCutoff_eq_zero_of_not_mem_ball hn]
      norm_num
    · rfl

section Glue

variable {e : ℕ} {X : Type} [TopologicalSpace X]

lemma chartBall_isOpen (B : FinHolAtlas e X) (j : Fin B.n) (ρ : ℝ) : IsOpen (chartBall B j ρ) :=
  (B.chart j).isOpen_inter_preimage isOpen_ball

lemma chartBall_mono (B : FinHolAtlas e X) (j : Fin B.n) {ρ ρ' : ℝ} (h : ρ ≤ ρ') :
    chartBall B j ρ ⊆ chartBall B j ρ' :=
  Set.inter_subset_inter_right _ (Set.preimage_mono (ball_subset_ball h))

open Classical in

def glueArg (B : FinHolAtlas e X) (f η : Fin B.n → X → ℝ) (δ Mb : ℝ) (j : Fin B.n) (y : X) : ℝ :=
  if y ∈ chartBall B j (5 / 4) then f j y + 4 * δ * η j y else -Mb - 10

lemma glue_local [T2Space X] (B : FinHolAtlas e X)
    (h2 : ∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target) (f η : Fin B.n → X → ℝ)
    (δ Mb : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hη0 : ∀ j, ∀ y ∈ chartBall B j 1, η j y = 0) (hη1 : ∀ j, ∀ y ∉ chartBall B j (9 / 8), η j y = -1)
    (hMb : ∀ j, ∀ y ∈ chartBall B j (5 / 4), |f j y| ≤ Mb)
    (hov : ∀ j k, ∀ y ∈ chartBall B j (5 / 4) ∩ chartBall B k (5 / 4), |f j y - f k y| ≤ δ)
    (y₀ : X) (k₀ : Fin B.n) (hk₀ : y₀ ∈ chartBall B k₀ 1) :
    ∃ W : Set X, IsOpen W ∧ y₀ ∈ W ∧ W ⊆ chartBall B k₀ 1 ∧
      (∀ j, y₀ ∈ chartBall B j (5 / 4) → W ⊆ chartBall B j (5 / 4)) ∧
      ∀ j, y₀ ∉ chartBall B j (5 / 4) → ∀ y ∈ W,
        glueArg B f η δ Mb j y + δ ≤ glueArg B f η δ Mb k₀ y := by
  classical
  have hcl : ∀ j, IsClosed ((B.chart j).symm '' closedBall (0 : Fin e → ℂ) (9 / 8)) := fun j =>
    ((isCompact_closedBall _ _).image_of_continuousOn ((B.chart j).continuousOn_symm.mono
      ((closedBall_subset_closedBall (by norm_num)).trans (h2 j)))).isClosed
  have hsub : ∀ j, chartBall B j (9 / 8) ⊆ (B.chart j).symm '' closedBall (0 : Fin e → ℂ) (9 / 8) := by
    intro j y hy
    exact ⟨B.chart j y, ball_subset_closedBall hy.2, (B.chart j).left_inv hy.1⟩
  have hnot : ∀ j, y₀ ∉ chartBall B j (5 / 4) →
      y₀ ∉ (B.chart j).symm '' closedBall (0 : Fin e → ℂ) (9 / 8) := by
    rintro j hj ⟨z, hz, rfl⟩
    have hzt : z ∈ (B.chart j).target := (closedBall_subset_closedBall (by norm_num)).trans (h2 j) hz
    apply hj
    refine ⟨(B.chart j).map_target hzt, ?_⟩
    show B.chart j ((B.chart j).symm z) ∈ ball (0 : Fin e → ℂ) (5 / 4)
    rw [(B.chart j).right_inv hzt]
    exact closedBall_subset_ball (by norm_num) hz
  obtain ⟨T, hT⟩ : ∃ T : Fin B.n → Set X, ∀ j, T j = if y₀ ∈ chartBall B j (5 / 4) then
      chartBall B j (5 / 4) else ((B.chart j).symm '' closedBall (0 : Fin e → ℂ) (9 / 8))ᶜ :=
    ⟨_, fun _ => rfl⟩
  refine ⟨chartBall B k₀ 1 ∩ ⋂ j, T j, ?_, ?_, Set.inter_subset_left, ?_, ?_⟩
  · refine (chartBall_isOpen B k₀ 1).inter (isOpen_iInter_of_finite fun j => ?_)
    rw [hT j]
    split_ifs
    · exact chartBall_isOpen B j _
    · exact (hcl j).isOpen_compl
  · refine ⟨hk₀, Set.mem_iInter.mpr fun j => ?_⟩
    rw [hT j]
    split_ifs with h
    · exact h
    · exact hnot j h
  · intro j hj y hy
    have hyj := Set.mem_iInter.mp hy.2 j
    rw [hT j, if_pos hj] at hyj
    exact hyj
  · intro j hj y hy
    have hyj := Set.mem_iInter.mp hy.2 j
    rw [hT j, if_neg hj] at hyj
    have hyk : y ∈ chartBall B k₀ (5 / 4) := chartBall_mono B k₀ (by norm_num) hy.1
    have hk : glueArg B f η δ Mb k₀ y = f k₀ y := by
      unfold glueArg
      rw [if_pos hyk, hη0 k₀ y hy.1, mul_zero, add_zero]
    rw [hk]
    unfold glueArg
    split_ifs with hy5
    · have hηj : η j y = -1 := hη1 j y (fun h => hyj (hsub j h))
      rw [hηj]
      have hd := (abs_le.mp (hov j k₀ y ⟨hy5, hyk⟩)).2
      nlinarith
    · have hm := (abs_le.mp (hMb k₀ y hyk)).1
      linarith

end Glue

def RegGlueStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A B : FinHolAtlas e X) (Θ th : LocPot X), A.Compatible B →
    (∀ x, ∃ j, x ∈ chartBall B j 1) → (∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target) →
    IsPotential A Θ → IsPosPot A Θ → IsPotential A th →
    ∃ K : ℝ, 0 < K ∧ ∀ (δ Mb : ℝ) (f : Fin B.n → X → ℝ), 0 < δ → δ ≤ 1 →
      (∀ j, A.SmoothOn (chartBall B j (5 / 4)) (f j)) →
      (∀ j, ∀ y ∈ chartBall B j (5 / 4), |f j y| ≤ Mb) →
      (∀ j, IsPshOn A (chartBall B j (5 / 4)) (th + LocPot.ofFun (f j))) →
      (∀ j k, ∀ y ∈ chartBall B j (5 / 4) ∩ chartBall B k (5 / 4), |f j y - f k y| ≤ δ) →
      ∃ F : X → ℝ, A.Smooth F ∧ IsPsh A (th + LocPot.ofFun F + Θ.rsmul (K * δ)) ∧
        ∀ j, ∀ y ∈ chartBall B j (5 / 4), |F y - f j y| ≤ K * δ

theorem reg_glue : RegGlueStatement := by
  intro e X _ _ _ A B Θ th hAB hcov h2 hΘ hΘpos hth
  classical
  obtain ⟨η, hη⟩ := glue_cutoff A B hAB h2
  have hηs : ∀ j, A.Smooth (η j) := fun j => (hη j).1

  have hC : ∀ j, ∃ C : ℝ, IsPsh A (LocPot.ofFun (η j) + Θ.rsmul C) := fun j =>
    pshShift A Θ hΘ hΘpos (η j) (hηs j)
  choose Cj hCj using hC
  set K' : ℝ := ∑ j, |Cj j| with hK'
  have hK'ge : ∀ j, Cj j ≤ K' := fun j =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |Cj j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j))
  have hK'0 : 0 ≤ K' := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨4 * K' + 2, by linarith, ?_⟩
  intro δ Mb f hδ hδ1 hfs hMb hfp hov
  by_cases hX : Nonempty X
  swap
  · refine ⟨fun _ => 0, fun k y hy => absurd ⟨(A.chart k).symm y⟩ hX, fun x => absurd ⟨x⟩ hX,
      fun j y => absurd ⟨y⟩ hX⟩
  obtain ⟨x₀⟩ := hX
  have : Nonempty (Fin B.n) := ⟨(hcov x₀).choose⟩
  set F : X → ℝ := fun y => ReciprocityTheory.AnForm.A.regMax δ (fun j => glueArg B f η δ Mb j y) with hF

  have hRM := (ReciprocityTheory.AnForm.A.regMax_thm (Fin B.n)).1 δ hδ

  have hΘlevi : ∀ x jA, ∀ y ∈ (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' Θ.U x, ∀ w : Fin e → ℂ,
      0 ≤ levi (Θ.φ x ∘ (A.chart jA).symm) y w := by
    intro x jA y hy w
    by_cases hw : w = 0
    · subst hw; simp [levi_zero]
    · exact (hΘpos x jA y hy w hw).le

  have hloc : ∀ y₀ : X, ∃ (W : Set X) (k₀ : Fin B.n) (I : Finset (Fin B.n)), IsOpen W ∧ y₀ ∈ W ∧
      W ⊆ chartBall B k₀ 1 ∧ k₀ ∈ I ∧ (∀ j ∈ I, W ⊆ chartBall B j (5 / 4)) ∧
      ∀ y ∈ W, F y = ReciprocityTheory.AnForm.A.regMax δ (fun j =>
        if j ∈ I then f j y + 4 * δ * η j y else f k₀ y + 4 * δ * η k₀ y - δ) := by
    intro y₀
    obtain ⟨k₀, hk₀⟩ := hcov y₀
    have hk₀' : y₀ ∈ chartBall B k₀ 1 := hk₀
    obtain ⟨W, hWo, hyW, hWk, hWin, hWout⟩ := glue_local B h2 f η δ Mb hδ.le hδ1
      (fun j => (hη j).2.2.1) (fun j => (hη j).2.2.2) hMb hov y₀ k₀ hk₀'
    let I : Finset (Fin B.n) := Finset.univ.filter fun j => y₀ ∈ chartBall B j (5 / 4)
    have hk₀I : k₀ ∈ I := by
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
      exact chartBall_mono B k₀ (by norm_num) hk₀'
    refine ⟨W, k₀, I, hWo, hyW, hWk, hk₀I, fun j hj => hWin j (by simpa [I] using hj), ?_⟩
    intro y hy
    have hy5 : ∀ j ∈ I, y ∈ chartBall B j (5 / 4) := fun j hj => hWin j (by simpa [I] using hj) hy
    show ReciprocityTheory.AnForm.A.regMax δ (fun j => glueArg B f η δ Mb j y) = _
    rw [regMax_dominated (Fin B.n) δ _ k₀ I hδ hk₀I (fun j hj =>
      hWout j (by simpa [I] using hj) y hy)]
    congr 1
    funext j
    have hk5 := hy5 k₀ hk₀I
    by_cases hj : j ∈ I
    · simp [hj, glueArg, hy5 j hj]
    · simp [hj, glueArg, hk5]

  have hbd : ∀ j, ∀ y ∈ chartBall B j (5 / 4), |F y - f j y| ≤ (4 * K' + 2) * δ := by
    intro j y hy
    have hup : ReciprocityTheory.AnForm.A.tmax (fun j' => glueArg B f η δ Mb j' y) ≤ f j y + δ := by
      apply ReciprocityTheory.AnForm.A.tmax_le
      intro j'
      unfold glueArg
      split_ifs with h'
      · have h1 := (abs_le.1 (hov j' j y ⟨h', hy⟩)).2
        have h2' : 4 * δ * η j' y ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith) ((hη j').2.1 y).2
        linarith
      · have := (abs_le.1 (hMb j y hy)).1
        linarith
    obtain ⟨k, hk⟩ := hcov y
    have hk5 : y ∈ chartBall B k (5 / 4) := chartBall_mono B k (by norm_num) hk
    have hlow : f j y - δ ≤ ReciprocityTheory.AnForm.A.tmax (fun j' => glueArg B f η δ Mb j' y) := by
      refine le_trans ?_ (ReciprocityTheory.AnForm.A.le_tmax _ k)
      have : glueArg B f η δ Mb k y = f k y := by
        simp [glueArg, hk5, (hη k).2.2.1 y hk]
      rw [this]
      have := (abs_le.1 (hov j k y ⟨hy, hk5⟩)).2
      linarith
    have h1 := (hRM.2.2.2.1 (fun j' => glueArg B f η δ Mb j' y)).1
    have h2' := (hRM.2.2.2.1 (fun j' => glueArg B f η δ Mb j' y)).2
    have hF' : F y = ReciprocityTheory.AnForm.A.regMax δ (fun j' => glueArg B f η δ Mb j' y) := rfl
    rw [abs_le]
    constructor <;> nlinarith

  have hsm : ∀ (jA : Fin A.n) (g : X → ℝ) (U : Set X), IsOpen U → A.SmoothOn U g →
      ∀ y ∈ (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' U,
        ContDiffAt ℝ ∞ (g ∘ (A.chart jA).symm) y := fun jA g U hU hg y hy =>
    (hg jA).contDiffAt (((A.chart jA).isOpen_inter_preimage_symm hU).mem_nhds hy)
  have hsmη : ∀ (jA : Fin A.n) (j : Fin B.n), ∀ y ∈ (A.chart jA).target,
      ContDiffAt ℝ ∞ (η j ∘ (A.chart jA).symm) y := fun jA j y hy =>
    hsm jA (η j) Set.univ isOpen_univ (hηs j) y ⟨hy, trivial⟩
  refine ⟨F, ?_, ?_, hbd⟩
  ·
    intro jA y' hy'
    have hyt : y' ∈ (A.chart jA).target := hy'.1
    obtain ⟨W, k₀, I, hWo, hyW, hWk, hk₀I, hWI, hWeq⟩ := hloc ((A.chart jA).symm y')
    have hV : (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' W ∈ nhds y' :=
      ((A.chart jA).isOpen_inter_preimage_symm hWo).mem_nhds ⟨hyt, hyW⟩
    let G : (Fin e → ℂ) → (Fin B.n → ℝ) := fun z j =>
      if j ∈ I then f j ((A.chart jA).symm z) + 4 * δ * η j ((A.chart jA).symm z)
      else f k₀ ((A.chart jA).symm z) + 4 * δ * η k₀ ((A.chart jA).symm z) - δ
    have hG : ContDiffAt ℝ ∞ G y' := by
      refine contDiffAt_pi.2 fun j => ?_
      by_cases hj : j ∈ I
      · simp only [G, hj, if_true]
        exact (hsm jA (f j) _ (chartBall_isOpen B j _) (hfs j) y' ⟨hyt, hWI j hj hyW⟩).add
          (contDiffAt_const.mul (hsmη jA j y' hyt))
      · simp only [G, hj, if_false]
        exact ((hsm jA (f k₀) _ (chartBall_isOpen B k₀ _) (hfs k₀) y'
          ⟨hyt, hWI k₀ hk₀I hyW⟩).add (contDiffAt_const.mul (hsmη jA k₀ y' hyt))).sub
          contDiffAt_const
    have hcomp : ContDiffAt ℝ ∞ (ReciprocityTheory.AnForm.A.regMax δ ∘ G) y' := hRM.1.contDiffAt.comp y' hG
    refine (hcomp.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hV] with z hz
    exact hWeq _ hz.2
  ·
    intro x jA y' hy' w
    have hyt : y' ∈ (A.chart jA).target := hy'.1
    have hyth : (A.chart jA).symm y' ∈ th.U x := hy'.2.1.1
    have hyΘ : (A.chart jA).symm y' ∈ Θ.U x := hy'.2.2
    obtain ⟨W, k₀, I, hWo, hyW, hWk, hk₀I, hWI, hWeq⟩ := hloc ((A.chart jA).symm y')
    set c : ℝ := (4 * K' + 2) * δ with hc
    set V := (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' (W ∩ th.U x ∩ Θ.U x) with hVdef
    have hVo : IsOpen V :=
      (A.chart jA).isOpen_inter_preimage_symm ((hWo.inter (th.isOpen_U x)).inter (Θ.isOpen_U x))
    have hyV : y' ∈ V := ⟨hyt, ⟨hyW, hyth⟩, hyΘ⟩
    let P : Fin B.n → (Fin e → ℂ) → ℝ := fun j z =>
      th.φ x ((A.chart jA).symm z) + (if j ∈ I then f j ((A.chart jA).symm z)
        else f k₀ ((A.chart jA).symm z) - δ)
    let Q : Fin B.n → (Fin e → ℂ) → ℝ := fun j z =>
      if j ∈ I then η j ((A.chart jA).symm z) else η k₀ ((A.chart jA).symm z)
    let R : (Fin e → ℂ) → ℝ := fun z => Θ.φ x ((A.chart jA).symm z)
    let u : Fin B.n → (Fin e → ℂ) → ℝ := fun j z => (P j z + 4 * δ * Q j z) + c * R z

    have hPs : ∀ j, ∀ z ∈ V, ContDiffAt ℝ ∞ (P j) z := by
      intro j z hz
      have hzt : z ∈ (A.chart jA).target := hz.1
      have h1 : ContDiffAt ℝ ∞ (th.φ x ∘ (A.chart jA).symm) z :=
        contDiffAt_of_isPotential A th hth x jA ⟨hzt, hz.2.1.2⟩
      by_cases hj : j ∈ I
      · simp only [P, hj, if_true]
        exact h1.add (hsm jA (f j) _ (chartBall_isOpen B j _) (hfs j) z ⟨hzt, hWI j hj hz.2.1.1⟩)
      · simp only [P, hj, if_false]
        exact h1.add ((hsm jA (f k₀) _ (chartBall_isOpen B k₀ _) (hfs k₀) z
          ⟨hzt, hWI k₀ hk₀I hz.2.1.1⟩).sub contDiffAt_const)
    have hQs : ∀ j, ∀ z ∈ V, ContDiffAt ℝ ∞ (Q j) z := by
      intro j z hz
      by_cases hj : j ∈ I
      · simp only [Q, hj, if_true]; exact hsmη jA j z hz.1
      · simp only [Q, hj, if_false]; exact hsmη jA k₀ z hz.1
    have hRs : ∀ z ∈ V, ContDiffAt ℝ ∞ R z := fun z hz =>
      contDiffAt_of_isPotential A Θ hΘ x jA ⟨hz.1, hz.2.2⟩
    have hus : ∀ j, ContDiffOn ℝ 2 (u j) V := by
      intro j z hz
      exact ((((hPs j z hz).add (contDiffAt_const.mul (hQs j z hz))).add
        (contDiffAt_const.mul (hRs z hz))).of_le (by norm_cast)).contDiffWithinAt

    have heq : ((th + LocPot.ofFun F + Θ.rsmul c).φ x ∘ (A.chart jA).symm) =ᶠ[nhds y']
        (fun z => ReciprocityTheory.AnForm.A.regMax δ (fun j => u j z)) := by
      filter_upwards [hVo.mem_nhds hyV] with z hz
      have hF' := hWeq _ hz.2.1.1
      show th.φ x ((A.chart jA).symm z) + F ((A.chart jA).symm z) +
          c * Θ.φ x ((A.chart jA).symm z) = _
      rw [hF']
      set C0 : ℝ := th.φ x ((A.chart jA).symm z) + c * Θ.φ x ((A.chart jA).symm z) with hC0
      have htr := hRM.2.2.2.2.2.2.1 (fun j => if j ∈ I then f j ((A.chart jA).symm z) +
          4 * δ * η j ((A.chart jA).symm z) else f k₀ ((A.chart jA).symm z) +
          4 * δ * η k₀ ((A.chart jA).symm z) - δ) C0
      have hu : (fun j => u j z) = (fun j => (if j ∈ I then f j ((A.chart jA).symm z) +
          4 * δ * η j ((A.chart jA).symm z) else f k₀ ((A.chart jA).symm z) +
          4 * δ * η k₀ ((A.chart jA).symm z) - δ) + C0) := by
        funext j
        by_cases hj : j ∈ I
        · simp only [u, P, Q, R, hj, if_true, hC0]; ring
        · simp only [u, P, Q, R, hj, if_false, hC0]; ring
      rw [hu, htr, hC0]
      ring
    rw [levi_congr heq w]
    refine ReciprocityTheory.AnForm.A.regMaxLevi_thm e (Fin B.n) δ V u hVo hδ hus y' hyV w 0 ?_
    intro j

    have hP2 := (hPs j y' hyV).of_le (show (2 : WithTop ℕ∞) ≤ ∞ by norm_cast)
    have hQ2 := (hQs j y' hyV).of_le (show (2 : WithTop ℕ∞) ≤ ∞ by norm_cast)
    have hR2 := (hRs y' hyV).of_le (show (2 : WithTop ℕ∞) ≤ ∞ by norm_cast)
    have hl1 : levi (u j) y' w = levi (P j) y' w + 4 * δ * levi (Q j) y' w + c * levi R y' w := by
      have e1 : levi (fun z => P j z + 4 * δ * Q j z) y' w =
          levi (P j) y' w + 4 * δ * levi (Q j) y' w := levi_add_smul (4 * δ) hP2 hQ2 w
      have e2 : levi (fun z => (P j z + 4 * δ * Q j z) + c * R z) y' w =
          levi (fun z => P j z + 4 * δ * Q j z) y' w + c * levi R y' w :=
        levi_add_smul c (hP2.add (contDiffAt_const.mul hQ2)) hR2 w
      simp only [u]; rw [e2, e1]
    have hRl : 0 ≤ levi R y' w := hΘlevi x jA y' ⟨hyt, hyΘ⟩ w

    have hPl : 0 ≤ levi (P j) y' w := by
      by_cases hj : j ∈ I
      · have := hfp j x jA y' ⟨hyt, ⟨hyth, trivial⟩, hWI j hj hyW⟩ w
        have hPe : P j = (th + LocPot.ofFun (f j)).φ x ∘ (A.chart jA).symm := by
          funext z; simp only [P, hj, if_true]; rfl
        rw [hPe]; exact this
      · have := hfp k₀ x jA y' ⟨hyt, ⟨hyth, trivial⟩, hWI k₀ hk₀I hyW⟩ w
        have hg2 : ContDiffAt ℝ 2 ((th + LocPot.ofFun (f k₀)).φ x ∘ (A.chart jA).symm) y' := by
          have h1 : ContDiffAt ℝ ∞ (th.φ x ∘ (A.chart jA).symm) y' :=
            contDiffAt_of_isPotential A th hth x jA ⟨hyt, hyth⟩
          exact (h1.add (hsm jA (f k₀) _ (chartBall_isOpen B k₀ _) (hfs k₀) y'
            ⟨hyt, hWI k₀ hk₀I hyW⟩)).of_le (by norm_cast)
        have hPe : P j = fun z => ((th + LocPot.ofFun (f k₀)).φ x ∘ (A.chart jA).symm) z +
            (-δ) * (fun _ => (1 : ℝ)) z := by
          funext z; simp only [P, hj, if_false]; show _ = th.φ x _ + f k₀ _ + _; ring
        rw [hPe, levi_add_smul (-δ) hg2 contDiffAt_const w]
        have h0 : levi (fun _ : Fin e → ℂ => (1 : ℝ)) y' w = 0 := by simp [levi]
        rw [h0]; linarith

    have hQl : 0 ≤ levi (Q j) y' w + K' * levi R y' w := by
      have key : ∀ j', Q j = η j' ∘ (A.chart jA).symm → 0 ≤ levi (Q j) y' w + K' * levi R y' w := by
        intro j' hQe
        have h0 := hCj j' x jA y' ⟨hyt, ⟨trivial, hyΘ⟩⟩ w
        have hQR : (LocPot.ofFun (η j') + Θ.rsmul (Cj j')).φ x ∘ (A.chart jA).symm =
            fun z => (η j' ∘ (A.chart jA).symm) z + Cj j' * R z := rfl
        rw [hQR, levi_add_smul (Cj j') (hsmη jA j' y' hyt |>.of_le (by norm_cast)) hR2 w] at h0
        rw [hQe]
        nlinarith [hK'ge j']
      by_cases hj : j ∈ I
      · exact key j (by funext z; simp [Q, hj])
      · exact key k₀ (by funext z; simp [Q, hj])
    rw [hl1]
    have : 0 ≤ 4 * δ * (levi (Q j) y' w + K' * levi R y' w) := by positivity
    have h2δ : 0 ≤ 2 * δ * levi R y' w := by positivity
    nlinarith

end

end ReciprocityTheory.AnForm.P
