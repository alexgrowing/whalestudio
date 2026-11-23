import Mathlib
import Formalism.PeriodIntegrals.CapelliEig
open Matrix MeasureTheory
noncomputable section
namespace GlobalTheory.Survey.MatrixExponentialEntries
open PI.UpqRep

abbrev M₁ := Matrix (Fin 1) (Fin 1) ℂ

def chi (m : ℤ) (g : M₁) : ℂ →L[ℂ] ℂ := (g 0 0) ^ m • ContinuousLinearMap.id ℂ ℂ

theorem norm_entry {ε : Fin 1 → Bool} {g : M₁} (hg : inUJ ε g) : ‖g 0 0‖ = 1 := by
  have h := congrFun (congrFun hg 0) 0
  simp only [Jm, Matrix.mul_apply, Fin.sum_univ_one, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at h
  have h2 := congrArg norm h
  have h3 : ‖(if ε 0 = true then (1 : ℂ) else -1)‖ = 1 := by split_ifs <;> simp
  simp only [norm_mul, norm_star, h3] at h2
  nlinarith [norm_nonneg (g 0 0)]

theorem wt_eq {ε : Fin 1 → Bool} (m : ℤ) (μ : Fin 1 → ℝ) (v : ℂ) (hv : v ≠ 0)
    (h : IsWtOn (Kset ε) (chi m) μ v) : μ = fun _ => (m : ℝ) := by
  have key : ∀ t : ℝ, Complex.exp ((((μ 0 - m) * t : ℝ) : ℂ) * Complex.I) = 1 := by
    intro t
    have hK : Matrix.diagonal (fun a : Fin 1 => Complex.exp (((fun _ => t) a : ℝ) * Complex.I)) ∈ Kset ε := by
      refine ⟨?_, ?_⟩
      · rw [Matrix.mem_unitaryGroup_iff]
        ext i j
        obtain rfl : i = 0 := Subsingleton.elim _ _
        obtain rfl : j = 0 := Subsingleton.elim _ _
        simp [Matrix.mul_apply, Matrix.star_apply, ← Complex.exp_conj, ← Complex.exp_add]
      · simp [Jm, Matrix.diagonal_mul_diagonal, mul_comm]
    have h1 := h (fun _ => t) hK
    simp only [chi, Matrix.diagonal_apply_eq, Fin.sum_univ_one, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul] at h1
    have h2 := mul_right_cancel₀ hv h1
    rw [← Complex.exp_int_mul] at h2
    have : (((μ 0 - m) * t : ℝ) : ℂ) * Complex.I = ((μ 0 * t : ℝ) : ℂ) * Complex.I - m * (t * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_sub, ← h2, div_self (Complex.exp_ne_zero _)]
  funext a
  obtain rfl : a = 0 := Subsingleton.elim _ _
  by_contra hne
  have hne' : μ 0 - m ≠ 0 := sub_ne_zero.2 hne
  have := key (Real.pi / (μ 0 - m))
  rw [mul_div_cancel₀ _ hne', Complex.exp_pi_mul_I] at this
  norm_num at this

theorem compact_one (ε : Fin 1 → Bool) : CompactSpace (UJ ε) := by
  have hc : IsCompact (Set.pi Set.univ fun _ : Fin 1 => Set.pi Set.univ fun _ : Fin 1 => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have h := (isClosedEmbeddingMatrix 1 ε).1.isCompact_preimage hc
  refine ⟨h.of_isClosed_subset isClosed_univ ?_⟩
  intro g _ i _ j _
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  simpa using (norm_entry g.2).le

theorem isDS_chi (ε : Fin 1 → Bool) (m : ℤ) : IsDS ε (fun _ => (m : ℝ)) (chi m) := by
  have hlow : lowK ε (fun _ => (m : ℝ)) = fun _ => (m : ℝ) := by
    funext a
    obtain rfl : a = 0 := Subsingleton.elim _ _
    simp [lowK, rhoN, rhoC, Finset.filter_singleton]
  have hsub : ∀ S : Submodule ℂ ℂ, S = ⊥ ∨ S = ⊤ := fun S => eq_bot_or_eq_top S
  have hiso : ∀ g ∈ UJset ε, ∀ v : ℂ, ‖chi m g v‖ = ‖v‖ := by
    intro g hg v
    simp [chi, norm_zpow, norm_entry hg]
  refine ⟨inferInstance, inferInstance, ⟨⟨?_, ?_⟩, hiso, ?_⟩, fun S _ _ => hsub S, ?_, ⟨⊤, ?_⟩, ?_⟩
  · ext; simp [chi]
  · intro a _ b _
    ext
    simp [chi, Matrix.mul_apply, mul_zpow, mul_comm]
  · intro v
    simp only [chi, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    refine ContinuousOn.mul (ContinuousOn.zpow₀ (by fun_prop) m ?_) continuousOn_const
    intro g hg
    left
    intro h0
    have := norm_entry hg
    simp [h0] at this
  · intro v w
    have := compact_one ε
    have hc : Continuous (coefOn (ε := ε) (chi m) v w) := by
      unfold coefOn
      simp only [chi, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
      refine Continuous.inner continuous_const (Continuous.mul (Continuous.zpow₀ ?_ m ?_) continuous_const)
      · exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem 0 0
      · intro g
        left
        intro h0
        have := norm_entry g.2
        simp [umat] at h0
        simp [h0] at this
    refine MemLp.of_bound hc.aestronglyMeasurable (‖w‖ * ‖v‖) (Filter.Eventually.of_forall fun g => ?_)
    have := norm_inner_le_norm (𝕜 := ℂ) w (chi m (umat g) v)
    rw [hiso _ g.2] at this
    exact this
  · rw [hlow]
    refine ⟨inferInstance, fun _ _ _ _ => trivial, fun S _ _ => hsub S, ⟨1, trivial, one_ne_zero, ?_⟩, ?_⟩
    · intro θ _
      simp only [chi, Matrix.diagonal_apply_eq, Fin.sum_univ_one, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul, ← Complex.exp_int_mul]
      congr 2
      push_cast; ring
    · intro μ v _ hv h
      rw [wt_eq m μ v hv h]
      exact ⟨fun _ _ => 0, by simp, by simp⟩
  · intro μ S hS
    obtain ⟨v, _, hv, h⟩ := hS.2.2.2.1
    rw [wt_eq m μ v hv h, hlow]

theorem exp_single_zero_zero_apply (z : ℂ) : (NormedSpace.exp (z • (Matrix.single 0 0 1 : M₁))) 0 0 = Complex.exp z := by
  have : z • (Matrix.single 0 0 1 : M₁) = Matrix.diagonal (fun _ => z) := by
    ext i j; fin_cases i; fin_cases j; simp
  rw [this, Matrix.exp_diagonal]
  simp [Pi.exp_def, Complex.exp_eq_exp_ℂ]

abbrev W₂ := EuclideanSpace ℂ (Fin 2)

end GlobalTheory.Survey.MatrixExponentialEntries
