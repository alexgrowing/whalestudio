import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExtB
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DeterminantCauchySchwarz

open Metric Real Filter Topology Matrix ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
open scoped ComplexOrder

noncomputable section

namespace LevelTowerAlt.Sg

theorem submean_of_small {g : ℂ → ℝ} (hc : ContinuousOn g (closedBall 0 1))
    (h : ∀ a ∈ ball (0 : ℂ) 1, ∃ s0 > 0, ∀ s, 0 < s → s < s0 → g a ≤ circleAverage g a s) :
    g 0 ≤ circleAverage g 0 1 := by
  obtain ⟨Φ, hΦc, hΦs, hΦ0, hΦm⟩ := poisson_ext one_pos (hc.mono sphere_subset_closedBall)
  rw [← hΦ0]
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  let k : ℂ → ℝ := fun ζ => g ζ - Φ ζ + δ * ‖ζ - 0‖ ^ 2
  have hq : Continuous fun ζ : ℂ => δ * ‖ζ - 0‖ ^ 2 := by fun_prop
  have hkc : ContinuousOn k (closedBall 0 1) := (hc.sub hΦc).add hq.continuousOn
  obtain ⟨a, ha, hmax⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_isMaxOn ⟨0, by simp⟩ hkc
  have h0 : k 0 ≤ k a := hmax (by simp)
  rcases (mem_closedBall.1 ha).lt_or_eq with hlt | heq
  · exfalso
    obtain ⟨s0, hs0, hs⟩ := h a hlt
    obtain ⟨s, hs1, hs2, hs3⟩ : ∃ s : ℝ, 0 < s ∧ s < s0 ∧ s < 1 - dist a 0 :=
      ⟨min s0 (1 - dist a 0) / 2, by have := lt_min hs0 (sub_pos.2 hlt); linarith,
        by have := lt_min hs0 (sub_pos.2 hlt); have := min_le_left s0 (1 - dist a 0); linarith,
        by have := lt_min hs0 (sub_pos.2 hlt); have := min_le_right s0 (1 - dist a 0); linarith⟩
    have hsub : closedBall a s ⊆ ball (0 : ℂ) 1 := closedBall_subset_ball' (by linarith)
    have hsph : sphere a s ⊆ closedBall (0 : ℂ) 1 :=
      sphere_subset_closedBall.trans (hsub.trans ball_subset_closedBall)
    have i1 : CircleIntegrable g a s := (hc.mono hsph).circleIntegrable hs1.le
    have i2 : CircleIntegrable Φ a s := (hΦc.mono hsph).circleIntegrable hs1.le
    have i3 : CircleIntegrable (fun ζ : ℂ => δ * ‖ζ - 0‖ ^ 2) a s := hq.continuousOn.circleIntegrable hs1.le
    have hle : circleAverage k a s ≤ k a := by
      apply circleAverage_mono_on_of_le_circle ((hkc.mono hsph).circleIntegrable hs1.le)
      intro x hx
      rw [abs_of_pos hs1] at hx
      exact hmax (hsph hx)
    have e1 : circleAverage k a s = circleAverage (fun ζ => g ζ - Φ ζ) a s +
        circleAverage (fun ζ : ℂ => δ * ‖ζ - 0‖ ^ 2) a s := circleAverage_fun_add (i1.sub i2) i3
    rw [e1, circleAverage_fun_sub i1 i2, cA_mul, circleAverage_norm_sub_sq a 0 hs1.le, hΦm a s hs1 hsub] at hle
    have h1 := hs s hs1 hs2
    have h2 : 0 < δ * s ^ 2 := by positivity
    have h3 : k a = g a - Φ a + δ * ‖a - 0‖ ^ 2 := rfl
    rw [h3] at hle
    linarith
  · have h1 : Φ a = g a := hΦs a heq
    have h2 : ‖a - 0‖ = 1 := by rwa [dist_eq_norm] at heq
    have h3 : k a = g a - Φ a + δ * ‖a - 0‖ ^ 2 := rfl
    have h4 : k 0 = g 0 - Φ 0 + δ * ‖(0 : ℂ) - 0‖ ^ 2 := rfl
    rw [h3, h4, h1, h2] at h0
    simp at h0
    linarith

theorem isPsh_of_tangent {n : ℕ} {U : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → ℝ} (hc : ContinuousOn f U)
    (h : ∀ t0 ∈ U, ∃ (V : Set (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ) (c : ℝ), IsOpen V ∧ t0 ∈ V ∧
      DifferentiableOn ℂ F V ∧ (∀ t ∈ V, F t ≠ 0) ∧ (∀ t ∈ V, 2 * log ‖F t‖ + c ≤ f t) ∧
      f t0 ≤ 2 * log ‖F t0‖ + c) : IsPsh U f := by
  refine ⟨hc.upperSemicontinuousOn, fun z w hd => ?_⟩
  have hl : Continuous fun ζ : ℂ => z + ζ • w := by fun_prop
  have hld : Differentiable ℂ fun ζ : ℂ => z + ζ • w := by fun_prop
  have hg : ContinuousOn (fun ζ : ℂ => f (z + ζ • w)) (closedBall 0 1) :=
    hc.comp hl.continuousOn fun ζ hζ => hd ζ (mem_closedBall_zero_iff.1 hζ)
  refine ⟨(hg.mono sphere_subset_closedBall).circleIntegrable zero_le_one, ?_⟩
  have := submean_of_small hg fun a ha => ?_
  · simpa using this
  obtain ⟨V, F, c, hVo, ht0, hF, hF0, hle, heq⟩ := h (z + a • w) (hd a (mem_ball_zero_iff.1 ha).le)
  have hW : IsOpen ((fun ζ : ℂ => z + ζ • w) ⁻¹' V ∩ ball 0 1) := (hVo.preimage hl).inter isOpen_ball
  obtain ⟨s0, hs0, hsub⟩ := Metric.isOpen_iff.1 hW a ⟨ht0, ha⟩
  refine ⟨s0, hs0, fun s hs hss => ?_⟩
  have hsub' := (closedBall_subset_ball hss).trans hsub
  have hφ : DifferentiableOn ℂ (fun ζ : ℂ => F (z + ζ • w)) ((fun ζ : ℂ => z + ζ • w) ⁻¹' V ∩ ball 0 1) :=
    hF.comp hld.differentiableOn fun ζ hζ => hζ.1
  have hH : InnerProductSpace.HarmonicOnNhd (fun ζ : ℂ => log ‖F (z + ζ • w)‖) (closedBall a |s|) := by
    intro ζ hζ
    rw [abs_of_pos hs] at hζ
    exact (hφ.analyticOnNhd hW ζ (hsub' hζ)).harmonicAt_log_norm (hF0 _ (hsub' hζ).1)
  have hav := hH.circleAverage_eq
  have i1 : CircleIntegrable (fun ζ : ℂ => log ‖F (z + ζ • w)‖) a s :=
    ContinuousOn.circleIntegrable'
      (fun ζ hζ => (hH ζ (sphere_subset_closedBall hζ)).1.continuousAt.continuousWithinAt)
  have i2 : CircleIntegrable (fun ζ : ℂ => 2 * log ‖F (z + ζ • w)‖) a s := i1.const_fun_smul (a := (2 : ℝ))
  have i3 : CircleIntegrable (fun _ : ℂ => c) a s := circleIntegrable_const _ _ _
  have i4 : CircleIntegrable (fun ζ : ℂ => f (z + ζ • w)) a s :=
    (hg.mono fun ζ hζ => ball_subset_closedBall (hsub' (sphere_subset_closedBall hζ)).2).circleIntegrable hs.le
  have hm : circleAverage (fun ζ : ℂ => 2 * log ‖F (z + ζ • w)‖ + c) a s ≤
      circleAverage (fun ζ : ℂ => f (z + ζ • w)) a s := by
    refine circleAverage_mono (i2.add i3) i4 fun ζ hζ => ?_
    rw [abs_of_pos hs] at hζ
    exact hle _ (hsub' (sphere_subset_closedBall hζ)).1
  rw [circleAverage_fun_add i2 i3, cA_mul, hav, circleAverage_const] at hm
  exact heq.trans hm

section MS

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {X : Type} [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] {U : Set X} {l m p : Type}

def MS (𝕜 : Type) [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {X : Type} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (U : Set X) {l m : Type} (A : X → Matrix l m ℂ) : Prop :=
  ∀ i j, ContDiffOn 𝕜 ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => A t i j) U

theorem MS.const (A : Matrix l m ℂ) : MS 𝕜 U (fun _ => A) := fun _ _ => contDiffOn_const

theorem MS.mono {A : X → Matrix l m ℂ} (h : MS 𝕜 U A) {V : Set X} (hV : V ⊆ U) : MS 𝕜 V A :=
  fun i j => (h i j).mono hV

theorem MS.mul [Fintype m] {A : X → Matrix l m ℂ} {B : X → Matrix m p ℂ} (hA : MS 𝕜 U A) (hB : MS 𝕜 U B) :
    MS 𝕜 U (fun t => A t * B t) := fun i j => by
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun k _ => (hA i k).mul (hB k j)

theorem MS.det [Fintype m] [DecidableEq m] {A : X → Matrix m m ℂ} (hA : MS 𝕜 U A) :
    ContDiffOn 𝕜 ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => (A t).det) U := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => hA _ _)

theorem MS.inv [Fintype m] [DecidableEq m] {A : X → Matrix m m ℂ} (hA : MS 𝕜 U A) (h : ∀ t ∈ U, (A t).det ≠ 0) :
    MS 𝕜 U (fun t => (A t)⁻¹) := fun i j => by
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul, Matrix.adjugate_apply]
  refine (hA.det.inv h).mul (MS.det fun a b => ?_)
  by_cases hab : a = j
  · subst hab
    simp only [Matrix.updateRow_self]
    exact contDiffOn_const
  · simp only [Matrix.updateRow_ne hab]
    exact hA a b

end MS

variable {n : ℕ} {U : Set (Fin n → ℂ)} {l m : Type}

theorem MS.real {A : (Fin n → ℂ) → Matrix l m ℂ} (h : MS ℂ U A) : MS ℝ U A :=
  fun i j => (h i j).restrict_scalars ℝ

theorem MS.ct {A : (Fin n → ℂ) → Matrix l m ℂ} (h : MS ℝ U A) : MS ℝ U (fun t => (A t)ᴴ) :=
  fun i j => Complex.conjCLE.contDiff.comp_contDiffOn (h j i)

theorem MS.of_diff (hU : IsOpen U) {A : (Fin n → ℂ) → Matrix l m ℂ}
    (h : ∀ i j, DifferentiableOn ℂ (fun t => A t i j) U) : MS ℂ U A :=
  fun i j => (ReciprocityTheory.AnForm.Osgood.osgood n U _ hU (h i j)).contDiffOn_of_completeSpace

variable {g : ℕ}

def lft (P : Matrix (Fin g ⊕ Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g ⊕ Fin g) ℂ :=
  (fromCols (1 : Matrix (Fin g) (Fin g) ℂ) (0 : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g ⊕ Fin g) ℂ) *
    ((fromCols P Pᴴᵀ)⁻¹ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ)

theorem tr_eq (P : Matrix (Fin g ⊕ Fin g) (Fin g) ℂ) (H : Matrix (Fin g) (Fin g) ℂ) :
    (P * H * Pᴴ)ᵀ = Pᴴᵀ * Hᵀ * (Pᴴᵀ)ᴴ := by
  have : (Pᴴᵀ)ᴴ = Pᵀ := by ext i j; simp
  rw [this, transpose_mul, transpose_mul, Matrix.mul_assoc]

theorem det_ne {P : Matrix (Fin g ⊕ Fin g) (Fin g) ℂ} {H : Matrix (Fin g) (Fin g) ℂ}
    (h : (P * H * Pᴴ - (P * H * Pᴴ)ᵀ).det ≠ 0) : (fromCols P Pᴴᵀ).det ≠ 0 := by
  have e : P * H * Pᴴ - (P * H * Pᴴ)ᵀ = fromCols P Pᴴᵀ * fromRows (H * Pᴴ) (-(Hᵀ * (Pᴴᵀ)ᴴ)) := by
    rw [fromCols_mul_fromRows, tr_eq, Matrix.mul_neg, Matrix.mul_assoc, Matrix.mul_assoc, sub_eq_add_neg]
  rw [e, det_mul] at h
  exact left_ne_zero_of_mul h

theorem lft_mul {P : Matrix (Fin g ⊕ Fin g) (Fin g) ℂ} (h : (fromCols P Pᴴᵀ).det ≠ 0) :
    lft P * P = 1 ∧ lft P * Pᴴᵀ = 0 := by
  rw [← fromCols_ext_iff, ← mul_fromCols, lft, Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h),
    Matrix.mul_one]

theorem sandwich {k : Type} (P : Matrix (Fin g ⊕ Fin g) (Fin g) ℂ) (H : Matrix (Fin g) (Fin g) ℂ)
    (X : Matrix k (Fin g ⊕ Fin g) ℂ) :
    X * (P * H * Pᴴ - (P * H * Pᴴ)ᵀ) * Xᴴ =
      (X * P) * H * (X * P)ᴴ - (X * Pᴴᵀ) * Hᵀ * (X * Pᴴᵀ)ᴴ := by
  rw [tr_eq, Matrix.mul_sub, Matrix.sub_mul, conjTranspose_mul, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem lft_sandwich {P : Matrix (Fin g ⊕ Fin g) (Fin g) ℂ} {H : Matrix (Fin g) (Fin g) ℂ}
    (h : (P * H * Pᴴ - (P * H * Pᴴ)ᵀ).det ≠ 0) :
    lft P * (P * H * Pᴴ - (P * H * Pᴴ)ᵀ) * (lft P)ᴴ = H := by
  obtain ⟨h1, h2⟩ := lft_mul (det_ne h)
  rw [sandwich, h1, h2]
  simp

variable {P : (Fin n → ℂ) → Matrix (Fin g ⊕ Fin g) (Fin g) ℂ} {H : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ}
  {K : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ}

theorem herm_smooth (hP : MS ℂ U P) (hK : K.det ≠ 0)
    (he : ∀ t ∈ U, P t * H t * (P t)ᴴ - (P t * H t * (P t)ᴴ)ᵀ = K) : MS ℝ U H := by
  have hQ : MS ℝ U (fun t => fromCols (P t) (P t)ᴴᵀ) := by
    rintro i (j | j)
    · exact hP.real i j
    · exact hP.real.ct j i
  have hL : MS ℝ U (fun t => lft (P t)) :=
    (MS.const _).mul (hQ.inv fun t ht => det_ne (H := H t) (by rw [he t ht]; exact hK))
  intro i j
  refine (((hL.mul (MS.const K)).mul hL.ct) i j).congr fun t ht => ?_
  show H t i j = (lft (P t) * K * (lft (P t))ᴴ) i j
  rw [← he t ht, lft_sandwich (by rw [he t ht]; exact hK)]

theorem local_frame (hU : IsOpen U) (hP : MS ℂ U P) (hK : K.det ≠ 0)
    (he : ∀ t ∈ U, P t * H t * (P t)ᴴ - (P t * H t * (P t)ᴴ)ᵀ = K) {t0 : Fin n → ℂ} (ht0 : t0 ∈ U) :
    ∃ (V : Set (Fin n → ℂ)) (G : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (C : Matrix (Fin g) (Fin g ⊕ Fin g) ℂ),
      IsOpen V ∧ t0 ∈ V ∧ V ⊆ U ∧ MS ℂ V G ∧ G t0 = 1 ∧ (∀ t ∈ V, G t * C * P t = 1) ∧ C * K * Cᴴ = H t0 := by
  have hK0 : (P t0 * H t0 * (P t0)ᴴ - (P t0 * H t0 * (P t0)ᴴ)ᵀ).det ≠ 0 := by rw [he t0 ht0]; exact hK
  have h1 := (lft_mul (det_ne hK0)).1
  have hG : MS ℂ U (fun t => lft (P t0) * P t) := (MS.const _).mul hP
  have hV : IsOpen (U ∩ (fun t => (lft (P t0) * P t).det) ⁻¹' {0}ᶜ) :=
    hG.det.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  refine ⟨_, fun t => (lft (P t0) * P t)⁻¹, lft (P t0), hV, ⟨ht0, ?_⟩, Set.inter_subset_left,
    (hG.mono Set.inter_subset_left).inv fun t ht => ht.2, ?_, fun t ht => ?_, ?_⟩
  · simp [h1]
  · simp [h1]
  · rw [Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_iff_ne_zero.2 ht.2)]
  · rw [← he t0 ht0, lft_sandwich hK0]

theorem logdet_psh (hU : IsOpen U) (hP : MS ℂ U P) (hK : K.det ≠ 0) (hH : ∀ t ∈ U, (H t).PosDef)
    (he : ∀ t ∈ U, P t * H t * (P t)ᴴ - (P t * H t * (P t)ᴴ)ᵀ = K) {k : ℕ}
    {u : (Fin n → ℂ) → Matrix (Fin k) (Fin g) ℂ} (hu : MS ℂ U u)
    (hli : ∀ t ∈ U, LinearIndependent ℂ (u t).row) :
    IsPsh U fun t => log (u t * H t * (u t)ᴴ).det.re := by
  have hpos : ∀ t ∈ U, 0 < (u t * H t * (u t)ᴴ).det := fun t ht =>
    ((hH t ht).mul_mul_conjTranspose_same (Matrix.vecMul_injective_iff.2 (hli t ht))).det_pos
  have hre : ∀ t ∈ U, 0 < (u t * H t * (u t)ᴴ).det.re := fun t ht => (Complex.pos_iff.1 (hpos t ht)).1
  refine isPsh_of_tangent ?_ fun t0 ht0 => ?_
  · have := ((hu.real.mul (herm_smooth hP hK he)).mul hu.real.ct).det.continuousOn
    exact (Complex.continuous_re.comp_continuousOn this).log fun t ht => (hre t ht).ne'
  obtain ⟨V, G, C, hVo, htV, hVU, hG, hG0, hGC, hC⟩ := local_frame hU hP hK he ht0
  have hF : MS ℂ V (fun t => u t * G t * H t0 * (u t0)ᴴ) :=
    ((((hu.mono hVU).mul hG).mul (MS.const _))).mul (MS.const _)
  have hW : IsOpen (V ∩ (fun t => (u t * G t * H t0 * (u t0)ᴴ).det) ⁻¹' {0}ᶜ) :=
    hF.det.continuousOn.isOpen_inter_preimage hVo isOpen_compl_singleton
  have hd0 := hre t0 ht0
  refine ⟨_, fun t => (u t * G t * H t0 * (u t0)ᴴ).det, -log (u t0 * H t0 * (u t0)ᴴ).det.re, hW, ⟨htV, ?_⟩,
    (hF.det.differentiableOn (by simp)).mono Set.inter_subset_left, fun t ht => ht.2, fun t ht => ?_, ?_⟩
  · simpa [hG0] using (hpos t0 ht0).ne'
  · have htU := hVU ht.1
    have h1 := Formalism.DivisionValues.determinant_cauchy_schwarz g k (H t0) (hH t0 ht0) (u t * G t) (u t0)
    have h2 := sandwich (P t) (H t) (u t * G t * C)
    have h3 : u t * G t * C * P t = u t := by
      rw [Matrix.mul_assoc (u t), Matrix.mul_assoc (u t), hGC t ht.1, Matrix.mul_one]
    have h4 : u t * G t * C * K * (u t * G t * C)ᴴ = u t * G t * H t0 * (u t * G t)ᴴ := by
      rw [← hC, conjTranspose_mul (u t * G t) C]
      simp only [Matrix.mul_assoc]
    rw [he t htU, h3, h4] at h2
    have h5 := Formalism.DivisionValues.det_le_det_add ((hH t0 ht0).posSemidef.mul_mul_conjTranspose_same (u t * G t))
      ((hH t htU).posSemidef.transpose.mul_mul_conjTranspose_same (u t * G t * C * (P t)ᴴᵀ))
    rw [h2, sub_add_cancel, ← h2] at h5
    have h6 := (Complex.le_def.1 h5).1
    have hn : 0 < ‖(u t * G t * H t0 * (u t0)ᴴ).det‖ := norm_pos_iff.2 ht.2
    have h7 := log_le_log (by positivity) (h1.trans (mul_le_mul_of_nonneg_right h6 hd0.le))
    rw [log_pow, log_mul (hre t htU).ne' hd0.ne'] at h7
    push_cast at h7
    linarith
  · have h1 : ‖(u t0 * H t0 * (u t0)ᴴ).det‖ = (u t0 * H t0 * (u t0)ᴴ).det.re :=
      (Complex.re_eq_norm.2 (hpos t0 ht0).le).symm
    simp only [hG0, Matrix.mul_one, h1]
    linarith

end LevelTowerAlt.Sg
