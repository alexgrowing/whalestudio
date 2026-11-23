import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate Pointwise

noncomputable section

namespace MainStatements.WeightKernel.PWeightDiag

def N {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ a, ∑ b, Complex.normSq (M a b)

def bump : ContDiffBump (1 : ℝ) := ⟨1/4, 1/2, by norm_num, by norm_num⟩

def θ : ℝ → ℝ := fun x => bump x

theorem θ_smooth : ContDiff ℝ ∞ θ := bump.contDiff
theorem θ_nonneg (x : ℝ) : 0 ≤ θ x := bump.nonneg
theorem θ_one : θ 1 = 1 := bump.one_of_mem_closedBall (by simp [bump])
theorem θ_supp {x : ℝ} (h : θ x ≠ 0) : 1/2 ≤ x ∧ x ≤ 3/2 := by
  have hs : x ∈ Function.support (bump : ℝ → ℝ) := Function.mem_support.mpr h
  rw [ContDiffBump.support_eq] at hs
  simp only [bump, Metric.mem_ball, Real.dist_eq, abs_lt] at hs
  constructor <;> linarith [hs.1, hs.2]

def Bw {n : ℕ} (l : Fin n → ℂ) (e : Fin n → MainStatements.WeightKernel.Mx n → MainStatements.WeightKernel.Mx n) : MainStatements.WeightKernel.Mx n × MainStatements.WeightKernel.Mx n → ℝ :=
  fun p => ∏ i ∈ Finset.univ.filter (fun i => 1 < ‖l i‖), θ (N (Matrix.of (e i p.1) * Matrix.of p.2))

theorem N_smul {n : ℕ} (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) : N (c • M) = ‖c‖ ^ 2 * N M := by
  simp only [N, Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul, Finset.mul_sum, Complex.normSq_eq_norm_sq, norm_mul, mul_pow]

theorem N_pos {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M ≠ 0) : 0 < N M := by
  obtain ⟨a, b, hab⟩ : ∃ a b, M a b ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hM (Matrix.ext hc)
  have h1 : 0 < Complex.normSq (M a b) := Complex.normSq_pos.mpr hab
  have h2 : Complex.normSq (M a b) ≤ ∑ b', Complex.normSq (M a b') :=
    Finset.single_le_sum (f := fun b' => Complex.normSq (M a b')) (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ b)
  have h3 : ∑ b', Complex.normSq (M a b') ≤ N M :=
    Finset.single_le_sum (f := fun a' => ∑ b', Complex.normSq (M a' b'))
      (fun _ _ => Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)) (Finset.mem_univ a)
  linarith

theorem single_mul_diag {n : ℕ} (i : Fin n) (τ : Fin n → ℂ) :
    single i i (1 : ℂ) * diagonal τ = τ i • single i i 1 := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  by_cases hb : b = i
  · subst hb
    rw [mul_comm]
  · have hb' : i ≠ b := fun h' => hb h'.symm
    simp [Matrix.single_apply, hb']

theorem comm_diag {n : ℕ} (l : Fin n → ℂ) (hl : Function.Injective l) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : M * diagonal l = diagonal l * M) : M = diagonal fun a => M a a := by
  ext a b
  have hab := congrFun (congrFun h a) b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hab
  by_cases e : a = b
  · subst e
    simp
  · rw [Matrix.diagonal_apply_ne _ e]
    have hne : l a ≠ l b := fun h' => e (hl h')
    have hz : M a b * (l b - l a) = 0 := by linear_combination hab
    rcases mul_eq_zero.mp hz with h0 | h0
    · exact h0
    · exact absurd (sub_eq_zero.mp h0).symm hne

end MainStatements.WeightKernel.PWeightDiag

private theorem weightDiag_lemma {n : ℕ} (i : Fin n) : MainStatements.WeightKernel.PWeightDiag.N (single i i (1 : ℂ)) = 1 := by
  simp only [MainStatements.WeightKernel.PWeightDiag.N, Matrix.single_apply, ite_and]
  simp [apply_ite Complex.normSq]

private theorem weightDiag_lemma_2 {n : ℕ} (i : Fin n) (τ : Fin n → ℂ) :
    diagonal τ * single i i (1 : ℂ) = τ i • single i i 1 := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  by_cases ha : a = i
  · subst ha
    rfl
  · have ha' : i ≠ a := fun h' => ha h'.symm
    simp [Matrix.single_apply, ha']

private theorem weightDiag_lemma_3 {n : ℕ} :
    Continuous (MainStatements.WeightKernel.PWeightDiag.N : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold MainStatements.WeightKernel.PWeightDiag.N
  exact continuous_finset_sum _ (fun a _ => continuous_finset_sum _
    (fun b _ => Complex.continuous_normSq.comp (continuous_id.matrix_elem a b)))

private theorem weightDiag_lemma_4 {n : ℕ} (f : MainStatements.WeightKernel.Mx n → MainStatements.WeightKernel.Mx n) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : MainStatements.WeightKernel.Mx n × MainStatements.WeightKernel.Mx n =>
      MainStatements.WeightKernel.PWeightDiag.N (Matrix.of (f p.1) * Matrix.of p.2)) := by
  have hent : ∀ a b, ContDiff ℝ ∞
      (fun p : MainStatements.WeightKernel.Mx n × MainStatements.WeightKernel.Mx n => (Matrix.of (f p.1) * Matrix.of p.2) a b) := by
    intro a b
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact ContDiff.sum (fun c _ => (contDiff_pi.mp (contDiff_pi.mp (hf.comp contDiff_fst) a) c).mul
      (contDiff_pi.mp (contDiff_pi.mp contDiff_snd c) b))
  unfold MainStatements.WeightKernel.PWeightDiag.N
  simp only [Complex.normSq_eq_norm_sq]
  exact ContDiff.sum (fun a _ => ContDiff.sum (fun b _ => (contDiff_norm_sq ℝ).comp (hent a b)))

open MainStatements.WeightKernel.PWeightDiag in
theorem MainStatements.WeightKernel.weightDiag : Lagr → ShiftT → BoundT → WeightDiag := by
  intro hLagr hShift hBound H _ _ _ _ _ _ _ _ n ι J hU s l hl hs hprop
  obtain ⟨hdet, hce, hrange⟩ := hU
  obtain ⟨e, he, hel⟩ := hLagr n l hl
  have hinj : Function.Injective ι := by
    intro x y hxy
    apply hce.injective
    show (fun a b => ι x a b) = fun a b => ι y a b
    rw [hxy]
  have hJl : (diagonal l)ᴴ * J * diagonal l = J := (hrange _).mp ⟨s, hs⟩
  have hinv : ∀ x : H, ι x⁻¹ * ι x = 1 ∧ ι x * ι x⁻¹ = 1 := fun x =>
    ⟨by rw [← map_mul, inv_mul_cancel, map_one], by rw [← map_mul, mul_inv_cancel, map_one]⟩
  have hdiag : ∀ w ∈ cent s, ι w = diagonal (fun a => ι w a a) := by
    intro w hw
    apply comm_diag l hl
    have hc : s * w = w * s := (Subgroup.mem_centralizer_iff.mp hw) s (Set.mem_singleton s)
    rw [← hs, ← map_mul, ← map_mul, hc]
  have hleft : ∀ w ∈ cent s, ∀ i, single i i (1 : ℂ) * ι w = ι w i i • single i i 1 := by
    intro w hw i
    calc single i i (1 : ℂ) * ι w = single i i 1 * diagonal (fun a => ι w a a) := congrArg _ (hdiag w hw)
      _ = ι w i i • single i i 1 := single_mul_diag i _
  have hright : ∀ w ∈ cent s, ∀ i, ι w * single i i (1 : ℂ) = ι w i i • single i i 1 := by
    intro w hw i
    calc ι w * single i i (1 : ℂ) = diagonal (fun a => ι w a a) * single i i 1 :=
          congrArg (· * single i i (1 : ℂ)) (hdiag w hw)
      _ = ι w i i • single i i 1 := weightDiag_lemma_2 i _
  have hcomm : ∀ w ∈ cent s, ∀ i, ι w * single i i (1 : ℂ) = single i i 1 * ι w := by
    intro w hw i
    rw [hleft w hw i, hright w hw i]
  have hF : ∀ (x y : H) (i : Fin n), N (Matrix.of (e i (matCoord ι (x⁻¹ * s * x))) * Matrix.of (matCoord ι y))
      = N (ι x⁻¹ * single i i 1 * ι x * ι y) := by
    intro x y i
    have h1 := hel i (ι x) (ι x⁻¹) (hinv x).1 (hinv x).2
    have h2 : matCoord ι (x⁻¹ * s * x) = fun a b => (ι x⁻¹ * diagonal l * ι x) a b := by
      funext a b
      simp only [matCoord, map_mul, hs]
    rw [h2, h1]
    rfl
  have Fpos : ∀ (x y : H) (i : Fin n), 0 < N (ι x⁻¹ * single i i 1 * ι y) := by
    intro x y i
    apply N_pos
    intro h0
    have key : ι x * (ι x⁻¹ * single i i 1 * ι y) * ι y⁻¹ = single i i 1 := by
      simp only [Matrix.mul_assoc]
      rw [(hinv y).2, Matrix.mul_one, ← Matrix.mul_assoc, (hinv x).2, Matrix.one_mul]
    rw [h0, Matrix.mul_zero, Matrix.zero_mul] at key
    have := congrFun (congrFun key i) i
    simp at this
  have hk : ∀ (x w y : H), w ∈ cent s → ∀ i,
      ι x⁻¹ * single i i 1 * ι x * ι (x⁻¹ * w * y) = ι w i i • (ι x⁻¹ * single i i 1 * ι y) := by
    intro x w y hw i
    rw [map_mul, map_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (ι x) (ι x⁻¹), (hinv x).2, Matrix.one_mul,
      ← Matrix.mul_assoc (single i i (1 : ℂ)) (ι w), hleft w hw i, Matrix.smul_mul, Matrix.mul_smul]
  refine ⟨Bw l e, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · unfold Bw
    apply contDiff_prod
    intro i _
    exact θ_smooth.comp (weightDiag_lemma_4 (e i) (he i))
  · intro z
    exact Finset.prod_nonneg (fun i _ => θ_nonneg _)
  · simp only [Bw]
    apply Finset.prod_pos
    intro i _
    have h1 : matCoord ι s = matCoord ι ((1 : H)⁻¹ * s * 1) := by simp
    rw [h1, hF]
    simp only [inv_one, map_one, Matrix.one_mul, Matrix.mul_one]
    rw [weightDiag_lemma, θ_one]
    norm_num
  · intro z h z' h'
    obtain ⟨τ, hτJ, hτ⟩ := hShift n J l hl hJl
      (fun i => N (ι z⁻¹ * single i i 1 * ι h) / N (ι z'⁻¹ * single i i 1 * ι h'))
      (fun i => div_pos (Fpos _ _ _) (Fpos _ _ _))
    obtain ⟨t₀, ht₀⟩ := (hrange (diagonal τ)).mpr hτJ
    have ht₀c : t₀ ∈ cent s := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      apply hinj
      rw [map_mul, map_mul, ht₀, hs, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext a
      exact mul_comm _ _
    refine ⟨t₀, ht₀c, fun t ht => ?_⟩
    simp only [Bw]
    apply Finset.prod_congr rfl
    intro i hi
    have hi' : 1 < ‖l i‖ := (Finset.mem_filter.mp hi).2
    congr 1
    have hσ : ‖τ i‖ ^ 2 = N (ι z⁻¹ * single i i 1 * ι h) / N (ι z'⁻¹ * single i i 1 * ι h') := hτ i hi'
    have htt : ι (t * t₀) i i = ι t i i * τ i := by
      rw [map_mul, ht₀, hdiag t ht, Matrix.diagonal_mul_diagonal]
      simp
    rw [hF, hF, hk z t h ht i, hk z' (t * t₀) h' (mul_mem ht ht₀c) i, N_smul, N_smul, htt, norm_mul,
      mul_pow, hσ, mul_assoc (‖ι t i i‖ ^ 2), div_mul_cancel₀ _ (Fpos z' h' i).ne']
  · intro C₁ C₂ hC₁ hC₂
    obtain ⟨C, hC, hCp⟩ := hprop C₁ hC₁
    obtain ⟨C', hC', hC'p⟩ := hprop C₂ hC₂
    have hιc : Continuous (fun x : H => ι x) := hce.continuous
    have hFc : ∀ i, Continuous (fun p : H × H => N (ι p.1⁻¹ * single i i 1 * ι p.2)) := fun i =>
      weightDiag_lemma_3.comp (((hιc.comp continuous_fst.inv).matrix_mul continuous_const).matrix_mul
        (hιc.comp continuous_snd))
    have hGc : Continuous (fun p : H × H => ∑ i, (N (ι p.1⁻¹ * single i i 1 * ι p.2)
        + (N (ι p.1⁻¹ * single i i 1 * ι p.2))⁻¹)) :=
      continuous_finset_sum _ (fun i _ => (hFc i).add ((hFc i).inv₀ (fun p => (Fpos p.1 p.2 i).ne')))
    obtain ⟨M0, hM0⟩ := (hC.prod hC').exists_bound_of_continuousOn hGc.continuousOn
    obtain ⟨M, hM1, hbd⟩ : ∃ M : ℝ, 1 ≤ M ∧ ∀ a ∈ C, ∀ b ∈ C', ∀ i,
        N (ι a⁻¹ * single i i 1 * ι b) ≤ M ∧ M⁻¹ ≤ N (ι a⁻¹ * single i i 1 * ι b) := by
      refine ⟨max M0 1, le_max_right _ _, fun a ha b hb i => ?_⟩
      have hP := Fpos a b i
      have h1 := hM0 (a, b) ⟨ha, hb⟩
      have h2 : N (ι a⁻¹ * single i i 1 * ι b) + (N (ι a⁻¹ * single i i 1 * ι b))⁻¹
          ≤ ∑ j, (N (ι a⁻¹ * single j j 1 * ι b) + (N (ι a⁻¹ * single j j 1 * ι b))⁻¹) :=
        Finset.single_le_sum (f := fun j => N (ι a⁻¹ * single j j 1 * ι b) + (N (ι a⁻¹ * single j j 1 * ι b))⁻¹)
          (fun j _ => by have := Fpos a b j; positivity) (Finset.mem_univ i)
      have h3 : ∑ j, (N (ι a⁻¹ * single j j 1 * ι b) + (N (ι a⁻¹ * single j j 1 * ι b))⁻¹) ≤ max M0 1 :=
        (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ h1).trans (le_max_left _ _))
      have hinvpos : 0 < (N (ι a⁻¹ * single i i 1 * ι b))⁻¹ := inv_pos.mpr hP
      refine ⟨by linarith, ?_⟩
      exact inv_le_of_inv_le₀ hP (by linarith)
    have hMpos : 0 < M := by linarith
    obtain ⟨R, hR⟩ := hBound n J l hdet hl hJl (1 / (2 * M)) (2 * M) (by positivity)
    have hQ : IsCompact (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : ℂ) R) :=
      isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall 0 R))
    refine ⟨(fun q : H × H × H => q.1⁻¹ * q.2.1 * q.2.2) ''
      (C ×ˢ (matCoord ι ⁻¹' (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : ℂ) R)) ×ˢ C'),
      (hC.prod ((hce.isCompact_preimage hQ).prod hC')).image (by fun_prop), ?_⟩
    intro z k hz hzk hB
    obtain ⟨t, ht, htz⟩ := hCp z hz
    obtain ⟨t', ht', ht'z⟩ := hC'p (z * k) hzk
    have hu : t * t'⁻¹ ∈ cent s := mul_mem ht (inv_mem ht')
    simp only [Bw] at hB
    have hB' := Finset.prod_ne_zero_iff.mp hB
    have hX : ∀ i, ι z⁻¹ * single i i 1 * ι z * ι k
        = ι (t * t'⁻¹) i i • (ι (t * z)⁻¹ * single i i 1 * ι (t' * (z * k))) := by
      intro i
      have e1 : ι z⁻¹ = ι (t * z)⁻¹ * ι t := by
        rw [← map_mul, show (t * z)⁻¹ * t = z⁻¹ by group]
      have e2 : ι z * ι k = ι t'⁻¹ * ι (t' * (z * k)) := by
        rw [← map_mul, ← map_mul, show t'⁻¹ * (t' * (z * k)) = z * k by group]
      rw [Matrix.mul_assoc _ (ι z) (ι k), e2, e1, Matrix.mul_assoc (ι (t * z)⁻¹) (ι t), hcomm t ht i]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (ι t) (ι t'⁻¹), ← map_mul, ← Matrix.mul_assoc (single i i (1 : ℂ)) (ι (t * t'⁻¹)),
        hleft _ hu i, Matrix.smul_mul, Matrix.mul_smul]
    have hτb : ∀ i, 1 < ‖l i‖ → 1 / (2 * M) ≤ ‖ι (t * t'⁻¹) i i‖ ∧ ‖ι (t * t'⁻¹) i i‖ ≤ 2 * M := by
      intro i hi
      have hfi := hB' i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
      have hsup := θ_supp hfi
      rw [hF, hX i, N_smul] at hsup
      obtain ⟨hlo, hhi⟩ := hbd _ htz _ ht'z i
      have hP := Fpos (t * z) (t' * (z * k)) i
      have hx0 : 0 ≤ ‖ι (t * t'⁻¹) i i‖ := norm_nonneg _
      have a1 : 1 / 2 ≤ ‖ι (t * t'⁻¹) i i‖ ^ 2 * M :=
        le_trans hsup.1 (mul_le_mul_of_nonneg_left hlo (sq_nonneg _))
      have a2 : ‖ι (t * t'⁻¹) i i‖ ^ 2 ≤ 3 / 2 * M := by
        have h4 : ‖ι (t * t'⁻¹) i i‖ ^ 2 * M⁻¹ ≤ 3 / 2 :=
          le_trans (mul_le_mul_of_nonneg_left hhi (sq_nonneg _)) hsup.2
        have h5 := mul_le_mul_of_nonneg_right h4 hMpos.le
        rwa [mul_assoc, inv_mul_cancel₀ hMpos.ne', mul_one] at h5
      constructor
      · rw [div_le_iff₀ (by positivity)]
        by_contra hc
        push_neg at hc
        have h6 : ‖ι (t * t'⁻¹) i i‖ * M < 1 / 2 := by linarith
        have h7 : ‖ι (t * t'⁻¹) i i‖ < 1 / 2 := by nlinarith
        nlinarith
      · by_contra hc
        push_neg at hc
        have h8 : 2 * M * (2 * M) < ‖ι (t * t'⁻¹) i i‖ * ‖ι (t * t'⁻¹) i i‖ :=
          mul_self_lt_mul_self (by positivity) hc
        nlinarith
    have hJu : (diagonal fun a => ι (t * t'⁻¹) a a)ᴴ * J * diagonal (fun a => ι (t * t'⁻¹) a a) = J := by
      rw [← hdiag _ hu]
      exact (hrange _).mp ⟨_, rfl⟩
    have hRu := hR (fun a => ι (t * t'⁻¹) a a) hJu hτb
    refine ⟨(t * z, t * t'⁻¹, t' * (z * k)), ⟨htz, ?_, ht'z⟩, ?_⟩
    · simp only [Set.mem_preimage, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
      intro a b
      show ‖ι (t * t'⁻¹) a b‖ ≤ R
      by_cases hab : a = b
      · subst hab
        exact hRu a
      · rw [hdiag _ hu, Matrix.diagonal_apply_ne _ hab, norm_zero]
        exact (norm_nonneg _).trans (hRu a)
    · show (t * z)⁻¹ * (t * t'⁻¹) * (t' * (z * k)) = k
      group
