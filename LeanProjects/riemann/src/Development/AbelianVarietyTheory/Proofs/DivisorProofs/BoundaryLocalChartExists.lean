import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M Topology Metric

noncomputable section
namespace GlobalTheory.AdaptedChart

variable {D : ℕ} {Y : Type} [TopologicalSpace Y]

theorem continuousOn_of_charts {E : Type} [TopologicalSpace E] (A : FinHolAtlas D Y) {U : Set Y}
    (hU : IsOpen U) {f : Y → E}
    (hf : ∀ j, ContinuousOn (f ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U)) :
    ContinuousOn f U := by
  intro y hy
  obtain ⟨j, hj⟩ := A.cover y
  have hT : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    (A.chart j).isOpen_inter_preimage_symm hU
  have hmem : A.chart j y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hy⟩
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j y) :=
    (hf j).continuousAt (hT.mem_nhds hmem)
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) y :=
    h1.comp ((A.chart j).continuousAt hj)
  have h3 : (f ∘ (A.chart j).symm) ∘ A.chart j =ᶠ[𝓝 y] f := by
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
    simp [(A.chart j).left_inv hz]
  exact (h2.congr h3).continuousWithinAt

def aff (c : Fin D → ℂ) (δ : ℝ) (hδ : δ ≠ 0) : (Fin D → ℂ) ≃ₜ (Fin D → ℂ) :=
  (Homeomorph.subRight c).trans (Homeomorph.smulOfNeZero ((δ : ℂ)⁻¹) (by simpa using hδ))

theorem aff_apply (c : Fin D → ℂ) (δ : ℝ) (hδ : δ ≠ 0) (z : Fin D → ℂ) :
    aff c δ hδ z = (δ : ℂ)⁻¹ • (z - c) := rfl

theorem aff_symm_apply (c : Fin D → ℂ) (δ : ℝ) (hδ : δ ≠ 0) (w : Fin D → ℂ) :
    (aff c δ hδ).symm w = (δ : ℂ) • w + c := by
  simp [aff, Homeomorph.smulOfNeZero, Units.smul_def]

def rescale (ψ : OpenPartialHomeomorph Y (Fin D → ℂ)) (c : Fin D → ℂ) (δ : ℝ) (hδ : δ ≠ 0) :
    OpenPartialHomeomorph Y (Fin D → ℂ) :=
  ((ψ.trans (aff c δ hδ).toOpenPartialHomeomorph).symm.restrOpen (ball 0 1) isOpen_ball).symm

theorem rescale_apply (ψ : OpenPartialHomeomorph Y (Fin D → ℂ)) (c : Fin D → ℂ) (δ : ℝ)
    (hδ : δ ≠ 0) (y : Y) : rescale ψ c δ hδ y = (δ : ℂ)⁻¹ • (ψ y - c) := by
  simp [rescale, aff_apply]

theorem rescale_symm_apply (ψ : OpenPartialHomeomorph Y (Fin D → ℂ)) (c : Fin D → ℂ) (δ : ℝ)
    (hδ : δ ≠ 0) (w : Fin D → ℂ) : (rescale ψ c δ hδ).symm w = ψ.symm ((δ : ℂ) • w + c) := by
  simp [rescale, aff_symm_apply]

theorem mem_ball_aff {c z : Fin D → ℂ} {δ : ℝ} (hδ : 0 < δ) :
    (δ : ℂ)⁻¹ • (z - c) ∈ ball (0 : Fin D → ℂ) 1 ↔ z ∈ ball c δ := by
  rw [mem_ball, mem_ball, dist_zero_right, dist_eq_norm, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hδ, inv_mul_lt_iff₀ hδ, mul_one]

theorem rescale_source (ψ : OpenPartialHomeomorph Y (Fin D → ℂ)) (c : Fin D → ℂ) {δ : ℝ}
    (hδ : 0 < δ) : (rescale ψ c δ hδ.ne').source = ψ.source ∩ ψ ⁻¹' ball c δ := by
  ext y
  have : y ∈ (rescale ψ c δ hδ.ne').source ↔ y ∈ ψ.source ∧ (δ : ℂ)⁻¹ • (ψ y - c) ∈ ball 0 1 := by
    simp [rescale, aff_apply]
  rw [this, mem_ball_aff hδ]; rfl

theorem rescale_target (ψ : OpenPartialHomeomorph Y (Fin D → ℂ)) (c : Fin D → ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hsub : ball c δ ⊆ ψ.target) : (rescale ψ c δ hδ.ne').target = ball 0 1 := by
  ext w
  have : w ∈ (rescale ψ c δ hδ.ne').target ↔ (δ : ℂ) • w + c ∈ ψ.target ∧ w ∈ ball 0 1 := by
    simp [rescale, aff_symm_apply]
  rw [this]
  refine ⟨fun h => h.2, fun h => ⟨hsub ?_, h⟩⟩
  have hw : (δ : ℂ)⁻¹ • (((δ : ℂ) • w + c) - c) = w := by
    rw [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hδ.ne'), one_smul]
  rw [← mem_ball_aff hδ, hw]; exact h

theorem analyticAt_aff (c : Fin D → ℂ) (a : ℂ) (w : Fin D → ℂ) :
    AnalyticAt ℂ (fun z : Fin D → ℂ => a • (z - c)) w := by
  fun_prop

theorem analyticAt_aff' (c : Fin D → ℂ) (a : ℂ) (w : Fin D → ℂ) :
    AnalyticAt ℂ (fun z : Fin D → ℂ => a • z + c) w := by
  fun_prop

open GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic in

theorem exists_adapted : ∀ (D : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] (A : ReciprocityTheory.AnForm.M.FinHolAtlas D Y) (L : ReciprocityTheory.AnForm.M.LocPot Y) (s : Y → Y → ℂ) (m : ℕ) (W : Fin m → Set Y), GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.IsBoundary A L s W → ∀ (y₀ : Y) (N : Set Y), IsOpen N → y₀ ∈ N → ∃ (Φ : OpenPartialHomeomorph Y (Fin D → ℂ)) (S : Finset (Fin D)) (K : Set Y) (a : ℝ), ReciprocityTheory.AnForm.M.IsCompatChart A Φ ∧ y₀ ∈ Φ.source ∧ Φ y₀ = 0 ∧ Φ.target = Metric.ball 0 1 ∧ IsCompact K ∧ Φ.source ⊆ K ∧ K ⊆ N ∧ (∀ y ∈ Φ.source, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s ↔ Φ y ∉ ReciprocityTheory.AnForm.A.coordDiv S) ∧ 0 ≤ a ∧ ∀ y ∈ Φ.source, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s → Real.log (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.rad L s y) ≤ a * Real.log (Real.exp 1 + ∑ i ∈ S, Real.log ‖Φ y i‖⁻¹) := by
  intro D Y _ _ _ A L s m W hB y₀ N hN hy₀N
  classical
  have hrad := fun y => exp_one_le_rad hB y
  obtain ⟨hPot, hSec, hSNC, -⟩ := hB
  obtain ⟨ψ, hψc, hy₀ψ, hψU, σ, hσinj, -, u, hu, hu0, hsu⟩ := hSNC y₀
  set c := ψ y₀ with hc
  let fac : Fin m → Y → ℂ := fun k y => (σ k).elim 1 (fun i => ψ y i)
  have hfac_some : ∀ k i y, σ k = some i → fac k y = ψ y i := by
    intro k i y h; simp [fac, h]
  have hfac_ne : ∀ k y, fac k y ≠ 0 ↔ ∀ i, σ k = some i → ψ y i ≠ 0 := by
    intro k y
    rcases h : σ k with _ | i
    · simp [fac, h]
    · simp [fac, h]
  have hsu' : ∀ y ∈ ψ.source, s y₀ y = u y * ∏ k, fac k y := by
    intro y hy
    rw [hsu y hy]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rcases h : σ k with _ | i <;> simp [fac, h]

  set V : Set (Fin D → ℂ) := {z | ∀ i, c i ≠ 0 → z i ≠ 0} with hVdef
  have hV : IsOpen V := by
    have : V = ⋂ i, {z : Fin D → ℂ | c i ≠ 0 → z i ≠ 0} := by ext z; simp [V]
    rw [this]
    refine isOpen_iInter_of_finite fun i => ?_
    by_cases hci : c i = 0
    · simp [hci]
    · simpa [hci] using isOpen_ne_fun (continuous_apply i) continuous_const
  set T := ψ.target ∩ ψ.symm ⁻¹' N ∩ V with hTdef
  have hT : IsOpen T := (ψ.isOpen_inter_preimage_symm hN).inter hV
  have hcT : c ∈ T := ⟨⟨ψ.map_source hy₀ψ, by simp [c, ψ.left_inv hy₀ψ, hy₀N]⟩, fun i h => h⟩
  obtain ⟨ε, hε, hεT⟩ := Metric.isOpen_iff.1 hT c hcT
  set δ := ε / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hδT : closedBall c δ ⊆ T := (closedBall_subset_ball (by linarith)).trans hεT
  have hballT : ball c δ ⊆ ψ.target :=
    fun z hz => (hδT (ball_subset_closedBall hz)).1.1
  set Φ := rescale ψ c δ hδ.ne' with hΦdef
  have hΦapp : ∀ y, Φ y = (δ : ℂ)⁻¹ • (ψ y - c) := rescale_apply ψ c δ hδ.ne'
  have hΦsymm : ∀ w, Φ.symm w = ψ.symm ((δ : ℂ) • w + c) := rescale_symm_apply ψ c δ hδ.ne'
  have hΦsrc : Φ.source = ψ.source ∩ ψ ⁻¹' ball c δ := rescale_source ψ c hδ
  have hΦtgt : Φ.target = ball 0 1 := rescale_target ψ c hδ hballT
  have hδC : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hΦS : ∀ y i, c i = 0 → Φ y i = (δ : ℂ)⁻¹ * ψ y i := by
    intro y i hci; rw [hΦapp]; simp [hci]
  set K := ψ.symm '' closedBall c δ with hKdef
  have hKψ : K ⊆ ψ.source := by
    rintro _ ⟨z, hz, rfl⟩; exact ψ.map_target (hδT hz).1.1
  have hKV : ∀ y ∈ K, ψ y ∈ V := by
    rintro _ ⟨z, hz, rfl⟩; rw [ψ.right_inv (hδT hz).1.1]; exact (hδT hz).2
  have hK : IsCompact K :=
    (isCompact_closedBall c δ).image_of_continuousOn
      (ψ.continuousOn_symm.mono fun z hz => (hδT hz).1.1)
  have hsrcK : Φ.source ⊆ K := by
    intro y hy
    rw [hΦsrc] at hy
    exact ⟨ψ y, ball_subset_closedBall hy.2, ψ.left_inv hy.1⟩
  have hsrcψ : ∀ y ∈ Φ.source, y ∈ ψ.source := fun y hy => by rw [hΦsrc] at hy; exact hy.1

  set S : Finset (Fin D) := Finset.univ.filter (fun i => ∃ k, σ k = some i ∧ c i = 0) with hSdef

  have hnz : ∀ y ∈ ψ.source, (s y y ≠ 0 ↔ s y₀ y ≠ 0) := by
    intro y hy
    have hn := hSec.2 y₀ y y ⟨hψU hy, L.mem_U y⟩
    have e1 := Real.exp_pos (-L.φ y y)
    have e2 := Real.exp_pos (-L.φ y₀ y)
    rw [ne_eq, ne_eq, ← norm_eq_zero, ← norm_eq_zero (a := s y₀ y)]
    constructor
    · intro h h0; apply h
      have : ‖s y y‖ * Real.exp (-L.φ y y) = 0 := by rw [← hn, h0, zero_mul]
      exact (mul_eq_zero.1 this).resolve_right e1.ne'
    · intro h h0; apply h
      have : ‖s y₀ y‖ * Real.exp (-L.φ y₀ y) = 0 := by rw [hn, h0, zero_mul]
      exact (mul_eq_zero.1 this).resolve_right e2.ne'
  have hopn : ∀ y ∈ ψ.source, (y ∈ opn s ↔ ∀ k, fac k y ≠ 0) := by
    intro y hy
    change s y y ≠ 0 ↔ _
    rw [hnz y hy, hsu' y hy, mul_ne_zero_iff, Finset.prod_ne_zero_iff]
    simp [hu0 y hy]
  have hdiv : ∀ y ∈ Φ.source, (y ∈ opn s ↔ Φ y ∉ ReciprocityTheory.AnForm.A.coordDiv S) := by
    intro y hy
    have hyψ := hsrcψ y hy
    have hyV : ψ y ∈ V := hKV y (hsrcK hy)
    rw [hopn y hyψ]
    simp only [ReciprocityTheory.AnForm.A.coordDiv, Set.mem_setOf_eq, not_exists, not_and]
    constructor
    · intro h i hi h0
      obtain ⟨k, hk, hci⟩ := (Finset.mem_filter.1 hi).2
      rw [hΦS y i hci, mul_eq_zero] at h0
      rcases h0 with h0 | h0
      · exact inv_ne_zero hδC h0
      · exact (hfac_ne k y).1 (h k) i hk h0
    · intro h k
      rw [hfac_ne]
      intro i hk
      by_cases hci : c i = 0
      · have hiS : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, k, hk, hci⟩
        intro h0; apply h i hiS; rw [hΦS y i hci, h0, mul_zero]
      · exact hyV i hci

  have hcompat : IsCompatChart A Φ := by
    intro j
    constructor
    · intro z hz
      have hz' : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source := ⟨hz.1, hsrcψ _ hz.2⟩
      have h1 := (hψc j).1 z hz'
      have : Φ ∘ (A.chart j).symm =
          (fun w : Fin D → ℂ => (δ : ℂ)⁻¹ • (w - c)) ∘ (ψ ∘ (A.chart j).symm) := by
        funext w; simp [hΦapp]
      rw [this]
      exact (analyticAt_aff c _ _).comp h1
    · intro w hw
      have hwb : w ∈ ball (0 : Fin D → ℂ) 1 := hΦtgt ▸ hw.1
      have hmem : (δ : ℂ) • w + c ∈ ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source := by
        refine ⟨hballT ?_, ?_⟩
        · rw [← mem_ball_aff hδ, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hδC, one_smul]
          exact hwb
        · have := hw.2
          simp only [Set.mem_preimage, hΦsymm] at this
          exact this
      have h2 := (hψc j).2 _ hmem
      have : A.chart j ∘ Φ.symm =
          (A.chart j ∘ ψ.symm) ∘ (fun w : Fin D → ℂ => (δ : ℂ) • w + c) := by
        funext w; simp [hΦsymm]
      rw [this]
      exact AnalyticAt.comp (g := A.chart j ∘ ψ.symm) (f := fun w : Fin D → ℂ => (δ : ℂ) • w + c) h2
        (analyticAt_aff' c _ w)
  have huc : ContinuousOn u ψ.source :=
    continuousOn_of_charts A ψ.open_source fun j => (hu j).continuousOn
  have hφc : ContinuousOn (L.φ y₀) (L.U y₀) :=
    continuousOn_of_charts A (L.isOpen_U y₀) fun j => (hPot.1 y₀ j).continuousOn
  have hfacc : ∀ k, ContinuousOn (fac k) ψ.source := by
    intro k
    rcases h : σ k with _ | i
    · simp only [fac, h, Option.elim]; exact continuousOn_const
    · simp only [fac, h, Option.elim]; exact (continuous_apply i).comp_continuousOn ψ.continuousOn
  set kS : Finset (Fin m) := Finset.univ.filter (fun k => ∃ i, σ k = some i ∧ c i = 0) with hkS
  set kN : Finset (Fin m) := Finset.univ.filter (fun k => ¬ ∃ i, σ k = some i ∧ c i = 0) with hkN
  let F : Y → ℝ := fun y =>
    -2 * Real.log ‖u y‖ + 2 * L.φ y₀ y - 2 * ∑ k ∈ kN, Real.log ‖fac k y‖
  have hFc : ContinuousOn F K := by
    refine ((continuousOn_const.mul ((huc.mono hKψ).norm.log fun y hy =>
      norm_ne_zero_iff.2 (hu0 y (hKψ hy)))).add
      (continuousOn_const.mul (hφc.mono fun y hy => hψU (hKψ hy)))).sub
      (continuousOn_const.mul (continuousOn_finset_sum _ fun k hk =>
        ((hfacc k).mono hKψ).norm.log fun y hy => ?_))
    rw [ne_eq, norm_eq_zero, ← ne_eq, hfac_ne]
    intro i hi
    have hci : c i ≠ 0 := fun h0 => (Finset.mem_filter.1 hk).2 ⟨i, hi, h0⟩
    exact hKV y hy i hci
  obtain ⟨B, hBd⟩ := hK.exists_bound_of_continuousOn hFc
  set B' := max 0 (B - 2 * (S.card * Real.log δ)) with hB'def
  have hB'0 : 0 ≤ B' := le_max_left _ _
  have hB'1 : B - 2 * (S.card * Real.log δ) ≤ B' := le_max_right _ _
  have he : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlog2 : 0 ≤ Real.log (2 + B') := Real.log_nonneg (by linarith)
  refine ⟨Φ, S, K, Real.log (2 + B') + 1, hcompat, ?_, ?_, hΦtgt, hK, hsrcK, ?_, hdiv, ?_, ?_⟩
  · rw [hΦsrc]; exact ⟨hy₀ψ, by simp [c, hδ]⟩
  · rw [hΦapp]; simp [c]
  · rintro _ ⟨z, hz, rfl⟩; exact (hδT hz).1.2
  · linarith
  · intro y hy hyo
    have hyψ := hsrcψ y hy
    have hfk : ∀ k, fac k y ≠ 0 := (hopn y hyψ).1 hyo
    have hsy : s y₀ y ≠ 0 := (hnz y hyψ).1 hyo
    have hn := hSec.2 y₀ y y ⟨hψU hyψ, L.mem_U y⟩
    have hlog : logNormSec L s y = Real.log ‖u y‖ + ∑ k, Real.log ‖fac k y‖ - L.φ y₀ y := by
      unfold logNormSec
      rw [← hn, Real.log_mul (norm_ne_zero_iff.2 hsy) (Real.exp_pos _).ne', Real.log_exp,
        hsu' y hyψ, norm_mul, norm_prod,
        Real.log_mul (norm_ne_zero_iff.2 (hu0 y hyψ))
          (Finset.prod_ne_zero_iff.2 fun k _ => norm_ne_zero_iff.2 (hfk k)),
        Real.log_prod (fun k _ => norm_ne_zero_iff.2 (hfk k))]
      ring
    have hsplit : ∑ k ∈ kS, Real.log ‖fac k y‖ + ∑ k ∈ kN, Real.log ‖fac k y‖ =
        ∑ k, Real.log ‖fac k y‖ := Finset.sum_filter_add_sum_filter_not _ _ _
    have hval : ∀ i, c i = 0 → ψ y i ≠ 0 →
        Real.log ‖ψ y i‖ = Real.log δ - Real.log ‖Φ y i‖⁻¹ := by
      intro i hci hne
      have h1 : ψ y i = (δ : ℂ) * Φ y i := by
        rw [hΦS y i hci, ← mul_assoc, mul_inv_cancel₀ hδC, one_mul]
      have hΦne : Φ y i ≠ 0 := by rw [hΦS y i hci]; exact mul_ne_zero (inv_ne_zero hδC) hne
      rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ,
        Real.log_mul hδ.ne' (norm_ne_zero_iff.2 hΦne), Real.log_inv]
      ring
    have hsum : ∑ k ∈ kS, Real.log ‖fac k y‖ = ∑ i ∈ S, (Real.log δ - Real.log ‖Φ y i‖⁻¹) := by
      refine Finset.sum_bij (fun k hk => Classical.choose (Finset.mem_filter.1 hk).2) ?_ ?_ ?_ ?_
      · intro k hk
        obtain ⟨h1, h2⟩ := Classical.choose_spec (Finset.mem_filter.1 hk).2
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, k, h1, h2⟩
      · intro k₁ hk₁ k₂ hk₂ h
        have e1 := (Classical.choose_spec (Finset.mem_filter.1 hk₁).2).1
        have e2 := (Classical.choose_spec (Finset.mem_filter.1 hk₂).2).1
        rw [h] at e1
        exact hσinj k₁ k₂ _ e1 e2
      · intro i hi
        obtain ⟨k, hk, hci⟩ := (Finset.mem_filter.1 hi).2
        have hkmem : k ∈ kS := Finset.mem_filter.2 ⟨Finset.mem_univ _, i, hk, hci⟩
        refine ⟨k, hkmem, ?_⟩
        have e1 := (Classical.choose_spec (Finset.mem_filter.1 hkmem).2).1
        exact (Option.some_injective _ (hk.symm.trans e1)).symm
      · intro k hk
        obtain ⟨h1, h2⟩ := Classical.choose_spec (Finset.mem_filter.1 hk).2
        rw [hfac_some k _ y h1]
        exact hval _ h2 ((hfac_ne k y).1 (hfk k) _ h1)
    have hFy : F y ≤ B := le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hBd y (hsrcK hy))
    set Λ := ∑ i ∈ S, Real.log ‖Φ y i‖⁻¹ with hΛdef
    have hradeq : rad L s y = Real.exp 1 + F y - 2 * (S.card * Real.log δ) + 2 * Λ := by
      unfold rad
      rw [hlog, ← hsplit, hsum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      simp only [F]
      ring
    have hΦball : ‖Φ y‖ < 1 := by
      have := Φ.map_source hy
      rwa [hΦtgt, mem_ball, dist_zero_right] at this
    have hΛ : 0 ≤ Λ := Finset.sum_nonneg fun i _ => by
      have hlt : ‖Φ y i‖ < 1 := lt_of_le_of_lt (norm_le_pi_norm (Φ y) i) hΦball
      rw [Real.log_inv]
      linarith [Real.log_nonpos (norm_nonneg (Φ y i)) hlt.le]
    have hT1 : Real.exp 1 ≤ Real.exp 1 + Λ := by linarith
    have hlogT : 1 ≤ Real.log (Real.exp 1 + Λ) := by
      have := Real.log_le_log (Real.exp_pos 1) hT1
      rwa [Real.log_exp] at this
    have hr_le : rad L s y ≤ (2 + B') * (Real.exp 1 + Λ) := by
      rw [hradeq]
      nlinarith [mul_nonneg hB'0 (sub_nonneg.2 he), mul_nonneg hB'0 hΛ]
    have hrpos : 0 < rad L s y := lt_of_lt_of_le (Real.exp_pos 1) (hrad y)
    calc Real.log (rad L s y) ≤ Real.log ((2 + B') * (Real.exp 1 + Λ)) :=
          Real.log_le_log hrpos hr_le
      _ = Real.log (2 + B') + Real.log (Real.exp 1 + Λ) :=
          Real.log_mul (by linarith) (by linarith [Real.exp_pos 1])
      _ ≤ (Real.log (2 + B') + 1) * Real.log (Real.exp 1 + Λ) := by
          nlinarith [mul_nonneg hlog2 (sub_nonneg.2 hlogT)]

end GlobalTheory.AdaptedChart
