import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.IfaceSt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.DecRepro

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_exp_neg (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (((-t : ℝ) : ℂ) • X))
      (-(X * NormedSpace.exp (((-t : ℝ) : ℂ) • X))) t := by
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-X) t
  have e : ∀ s : ℝ, s • (-X) = ((-s : ℝ) : ℂ) • X := fun s => by
    rw [Complex.coe_smul, smul_neg, neg_smul]
  simp only [e, neg_mul] at h
  exact h

theorem inG_cpart (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (Formalism.REAL.cpart1 ε Z) ∧ inG ε (Formalism.REAL.cpart2 ε Z) := by
  constructor <;>
  · ext a b
    simp only [Formalism.REAL.cpart1, Formalism.REAL.cpart2, Formalism.REAL.Jm, Jm, Matrix.add_apply, Matrix.sub_apply,
      Matrix.mul_diagonal, Matrix.diagonal_mul, conjTranspose_apply, Matrix.smul_apply,
      Matrix.zero_apply, smul_eq_mul]
    split_ifs <;> simp <;> ring

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def kerD (β : Matrix (Fin n) (Fin n) ℂ → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ := fun y => -(fderiv ℝ β y (X * y))

theorem kerD_smooth {β : Matrix (Fin n) (Fin n) ℂ → ℂ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (X : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (kerD β X) ∧ HasCompactSupport (kerD β X) := by
  refine ⟨?_, ?_⟩
  · exact ((hβ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply
      (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ X)).contDiff).neg
  · refine (hβc.fderiv ℝ).mono fun y hy => ?_
    intro h0
    exact hy (by simp [kerD, h0])

variable {ε : Fin n → Bool}

theorem integrable_ker (ν : Measure (S7.UJ ε)) [ν.IsHaarMeasure] {β φ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hβ : Continuous β) (hβc : HasCompactSupport β) (hφ : ContinuousOn φ (UJset ε))
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    Continuous (fun y : S7.UJ ε => φ (g * S7.toM y)) ∧
      Integrable (fun y : S7.UJ ε => β (S7.toM y) * φ (g * S7.toM y)) ν := by
  obtain ⟨u, rfl⟩ : g ∈ Set.range (fun g : S7.UJ ε => S7.toM g) := by rw [S7.range_toM]; exact hg
  have hc : Continuous (fun y : S7.UJ ε => φ (S7.toM u * S7.toM y)) :=
    hφ.comp_continuous (continuous_const.matrix_mul (S7.continuous_toM ε)) fun y => (u * y).2
  exact ⟨hc, ((hβ.comp (S7.continuous_toM ε)).mul hc).integrable_of_hasCompactSupport
    (hβc.comp_isClosedEmbedding (S7.isClosedEmbedding_toM ε)).mul_right⟩

theorem hasDerivAt_conv (ν : Measure (S7.UJ ε)) [ν.IsHaarMeasure] {β φ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hβ : ContDiff ℝ (⊤ : ℕ∞) β) (hβc : HasCompactSupport β) (hφ : ContinuousOn φ (UJset ε))
    {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => ∫ y, β (S7.toM y) *
        φ (g * NormedSpace.exp ((t : ℂ) • X) * S7.toM y) ∂ν)
      (∫ y, kerD β X (S7.toM y) * φ (g * S7.toM y) ∂ν) 0 := by
  set γ : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => NormedSpace.exp (((-t : ℝ) : ℂ) • X) with hγ
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_exp_neg X t).continuousAt
  have hinv : ∀ t : ℝ, γ t * γ (-t) = 1 ∧ γ (-t) * γ t = 1 := fun t => by
    constructor <;> simp only [hγ] <;> rw [← exp_add_smul] <;> simp
  have hshift : ∀ t : ℝ, ∫ y, β (S7.toM y) * φ (g * NormedSpace.exp ((t : ℂ) • X) * S7.toM y) ∂ν =
      ∫ y, β (γ t * S7.toM y) * φ (g * S7.toM y) ∂ν := by
    intro t
    obtain ⟨u, hu⟩ : γ t ∈ Set.range (fun g : S7.UJ ε => S7.toM g) := by
      rw [S7.range_toM]; exact exp_smul_mem_UJset hX (-t)
    rw [← integral_mul_left_eq_self _ u]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    have e1 : S7.toM (u * y) = γ t * S7.toM y := by rw [← hu]; rfl
    have e2 : NormedSpace.exp ((t : ℂ) • X) = γ (-t) := by simp [hγ]
    simp only [e1, e2]
    rw [Matrix.mul_assoc g, ← Matrix.mul_assoc (γ (-t)), (hinv t).2, Matrix.one_mul]
  simp only [hshift]
  obtain ⟨hφc, -⟩ := integrable_ker ν hβ.continuous hβc hφ hg
  obtain ⟨hk, hkc⟩ := kerD_smooth hβ hβc X

  set Kc : Set (S7.UJ ε) := (fun y : S7.UJ ε => S7.toM y) ⁻¹'
    ((fun p : ℝ × Matrix (Fin n) (Fin n) ℂ => γ (-p.1) * p.2) ''
      (Metric.closedBall (0 : ℝ) 1 ×ˢ tsupport (kerD β X))) with hKc
  have hKcc : IsCompact Kc := (S7.isClosedEmbedding_toM ε).isCompact_preimage
    (((isCompact_closedBall _ _).prod hkc).image
      ((hγc.comp continuous_fst.neg).matrix_mul continuous_snd))
  obtain ⟨C1, hC1⟩ := hk.continuous.bounded_above_of_compact_support hkc
  obtain ⟨C2, hC2⟩ := hKcc.exists_bound_of_continuousOn hφc.continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (𝕜 := ℝ) (x₀ := (0 : ℝ))
    (F := fun t y => β (γ t * S7.toM y) * φ (g * S7.toM y))
    (F' := fun t y => kerD β X (γ t * S7.toM y) * φ (g * S7.toM y))
    (bound := Kc.indicator fun _ => C1 * C2) (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun t => ((hβ.continuous.comp
      (continuous_const.matrix_mul (S7.continuous_toM ε))).mul hφc).aestronglyMeasurable)
    (by simpa [hγ] using (integrable_ker ν hβ.continuous hβc hφ hg).2)
    (((hk.continuous.comp
      (continuous_const.matrix_mul (S7.continuous_toM ε))).mul hφc).aestronglyMeasurable)
    (ae_of_all _ fun y t ht => by
      by_cases hy : y ∈ Kc
      · rw [Set.indicator_of_mem hy, norm_mul]
        exact mul_le_mul (hC1 _) (hC2 y hy) (norm_nonneg _) ((norm_nonneg _).trans (hC1 0))
      · rw [Set.indicator_of_notMem hy]
        have : kerD β X (γ t * S7.toM y) = 0 := by
          by_contra h0
          refine hy ⟨(t, γ t * S7.toM y), ⟨Metric.ball_subset_closedBall ht,
            subset_tsupport _ h0⟩, ?_⟩
          simp only []
          rw [← Matrix.mul_assoc, (hinv t).2, Matrix.one_mul]
        simp [this])
    ((integrable_indicator_iff hKcc.measurableSet).mpr (integrableOn_const hKcc.measure_lt_top.ne))
    (ae_of_all _ fun y t _ => by
      have h1 := (LinearMap.toContinuousLinearMap
        (LinearMap.mulRight ℝ (S7.toM y))).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_neg X t)
      have h2 := ((hβ.differentiable (by simp)) (γ t * S7.toM y)).hasFDerivAt.comp_hasDerivAt t h1
      have h3 := h2.mul_const (φ (g * S7.toM y))
      refine HasDerivAt.congr_deriv h3 ?_
      show fderiv ℝ β (γ t * S7.toM y) (-(X * γ t) * S7.toM y) * _ = _
      rw [Matrix.neg_mul, Matrix.mul_assoc, map_neg, kerD])
  simpa [hγ] using key.2

theorem eword_conv (ν : Measure (S7.UJ ε)) [ν.IsHaarMeasure] {β φ f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hβ : ContDiff ℝ (⊤ : ℕ∞) β) (hβc : HasCompactSupport β) (hφ : ContinuousOn φ (UJset ε))
    (hf : ∀ g ∈ UJset ε, f g = ∫ y, β (S7.toM y) * φ (g * S7.toM y) ∂ν) (w : List (Fin n × Fin n)) :
    ∃ βw : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) βw ∧ HasCompactSupport βw ∧
      ∀ g ∈ UJset ε, Formalism.REAL.Eword ε w f g = ∫ y, βw (S7.toM y) * φ (g * S7.toM y) ∂ν := by
  induction w with
  | nil => exact ⟨β, hβ, hβc, hf⟩
  | cons p w ih =>
    obtain ⟨b, hb, hbc, hw⟩ := ih
    have hR : ∀ X, inG ε X → ∀ g ∈ UJset ε, Formalism.REAL.Rd X (Formalism.REAL.Eword ε w f) g =
        ∫ y, kerD b X (S7.toM y) * φ (g * S7.toM y) ∂ν := by
      intro X hX g hg
      rw [← (hasDerivAt_conv ν hb hbc hφ hg hX).deriv, Formalism.REAL.Rd]
      congr 1
      funext t
      refine hw _ ?_
      have h1 : gᴴ * Jm ε * g = Jm ε := hg
      have h2 : (NormedSpace.exp ((t : ℂ) • X))ᴴ * Jm ε * NormedSpace.exp ((t : ℂ) • X) = Jm ε :=
        exp_smul_mem_UJset hX t
      show (g * NormedSpace.exp ((t : ℂ) • X))ᴴ * Jm ε * (g * NormedSpace.exp ((t : ℂ) • X)) = Jm ε
      rw [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Jm ε),
        ← Matrix.mul_assoc gᴴ, ← Matrix.mul_assoc gᴴ, h1, ← Matrix.mul_assoc, h2]
    obtain ⟨hX1, hX2⟩ := inG_cpart ε (Matrix.single p.1 p.2 1)
    obtain ⟨a1, c1⟩ := kerD_smooth hb hbc (Formalism.REAL.cpart1 ε (Matrix.single p.1 p.2 1))
    obtain ⟨a2, c2⟩ := kerD_smooth hb hbc (Formalism.REAL.cpart2 ε (Matrix.single p.1 p.2 1))
    refine ⟨fun y => kerD b _ y + Complex.I * kerD b _ y, a1.add (contDiff_const.mul a2),
      c1.add c2.mul_left, fun g hg => ?_⟩
    show Formalism.REAL.Rd _ _ g + Complex.I * Formalism.REAL.Rd _ _ g = _
    rw [hR _ hX1 g hg, hR _ hX2 g hg, ← integral_const_mul, ← integral_add
      (integrable_ker ν a1.continuous c1 hφ hg).2
      ((integrable_ker ν a2.continuous c2 hφ hg).2.const_mul _)]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only []; ring

theorem eword_repro {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (μ : Fin n → ℤ) (ν : Measure (S7.UJ ε)) [ν.IsHaarMeasure]
    (hcont : ContinuousOn (S7.PsiM T μ) (UJset ε)) (β : Matrix (Fin n) (Fin n) ℂ → ℂ) (M : T.V →L[ℂ] T.V) (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β)
    (hrep : ∀ g ∈ UJset ε, S7.PsiM T μ g = (∫ y, β (S7.toM y) • S7.PsiM T μ (g * S7.toM y) ∂ν) * M)
    (w : List (Fin n × Fin n)) (v₁ v₂ : T.V) :
    ∃ βw : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) βw ∧ HasCompactSupport βw ∧
      ∀ g ∈ UJset ε, Formalism.REAL.Eword ε w (fun y => ⟪v₂, S7.PsiM T μ y v₁⟫_ℂ) g =
        ∫ y, βw (S7.toM y) * ⟪v₂, S7.PsiM T μ (g * S7.toM y) (M v₁)⟫_ℂ ∂ν := by
  let L : (T.V →L[ℂ] T.V) →L[ℂ] ℂ := (innerSL ℂ v₂).comp (ContinuousLinearMap.apply ℂ T.V (M v₁))
  refine eword_conv ν (φ := fun y => L (S7.PsiM T μ y)) hβ hβc
    (L.continuous.comp_continuousOn hcont) (fun g hg => ?_) w
  obtain ⟨u, rfl⟩ : g ∈ Set.range (fun g : S7.UJ ε => S7.toM g) := by rw [S7.range_toM]; exact hg
  have hc : Continuous (fun y : S7.UJ ε => S7.PsiM T μ (S7.toM u * S7.toM y)) :=
    hcont.comp_continuous (continuous_const.matrix_mul (S7.continuous_toM ε)) fun y => (u * y).2
  have hi : Integrable (fun y : S7.UJ ε => β (S7.toM y) • S7.PsiM T μ (S7.toM u * S7.toM y)) ν :=
    ((hβ.continuous.comp (S7.continuous_toM ε)).smul hc).integrable_of_hasCompactSupport
      (hβc.comp_isClosedEmbedding (S7.isClosedEmbedding_toM ε)).smul_right
  have h1 := L.integral_comp_comm hi
  simp only [map_smul, smul_eq_mul] at h1
  rw [h1]
  simp only []
  rw [hrep _ hg]
  rfl

end ReciprocityTheory.ChartRestriction.DS.Lap.S0.DecRepro
