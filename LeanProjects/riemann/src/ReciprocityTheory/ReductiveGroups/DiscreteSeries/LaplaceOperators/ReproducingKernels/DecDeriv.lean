import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.IfaceSt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiDecayCore
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IntegrableOfDecayVG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.DecDerivA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.DecRepro
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PsiFunct

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.DecDeriv

open ReciprocityTheory.ChartRestriction.DS

section FrobF

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

lemma frob_eq_norm {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) : frob a = ‖a‖ := S7.sqrt_hs_frobVG a

theorem frob_mul_le {n : ℕ} (a b : Matrix (Fin n) (Fin n) ℂ) : frob (a * b) ≤ frob a * frob b := by
  rw [frob_eq_norm, frob_eq_norm, frob_eq_norm]
  exact Matrix.frobenius_norm_mul a b

theorem frob_kexp_le {n : ℕ} (ε : Fin n → Bool) (k : S7.KG ε) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : inP ε X) :
    frob (S7.toMK k * NormedSpace.exp X) ≤ Real.sqrt n * Real.exp (Real.sqrt (S7.hs X)) := by
  show Real.sqrt (S7.hs _) ≤ _
  rw [S7.hs_kmulVG, S7.sqrt_hs_frobVG, S7.sqrt_hs_frobVG]
  exact S7.norm_exp_frobVG X

end FrobF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma frob_eq_sqrt_hs {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) : frob a = Real.sqrt (S7.hs a) := rfl

lemma norm_sgn {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : ‖(if ε a then (1 : ℂ) else -1)‖ = 1 := by
  split_ifs <;> simp

theorem one_le_frob {n : ℕ} (hn : 0 < n) (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : g ∈ UJset ε) : 1 ≤ frob g := by
  classical
  set i0 : Fin n := ⟨0, hn⟩
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have h := congrFun (congrFun hg' i0) i0
  rw [Matrix.mul_apply] at h
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_apply_eq, Matrix.conjTranspose_apply] at h
  have h1 : (1 : ℝ) ≤ ∑ x, ‖g x i0‖ ^ 2 := by
    calc (1 : ℝ) = ‖(if ε i0 then (1 : ℂ) else -1)‖ := (norm_sgn ε i0).symm
      _ = ‖∑ x, star (g x i0) * (if ε x then (1 : ℂ) else -1) * g x i0‖ := by rw [h]
      _ ≤ ∑ x, ‖star (g x i0) * (if ε x then (1 : ℂ) else -1) * g x i0‖ := norm_sum_le _ _
      _ = ∑ x, ‖g x i0‖ ^ 2 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [norm_mul, norm_mul, norm_sgn, norm_star]; ring
  have h2 : ∑ x, ‖g x i0‖ ^ 2 ≤ ∑ i, ∑ j, ‖g i j‖ ^ 2 :=
    Finset.sum_le_sum fun x _ => Finset.single_le_sum (f := fun j => ‖g x j‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i0)
  unfold frob
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (h1.trans h2)

theorem frob_inv {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : g ∈ UJset ε) :
    frob g⁻¹ = frob g := by
  classical
  have hl := S7.left_inv_of_inUJ ε g hg
  rw [Matrix.inv_eq_left_inv hl]
  unfold frob
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, norm_mul, norm_star,
    norm_sgn, one_mul, mul_one]

theorem psiM_frob_dec {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (T : S7.KType ε (lowK ε lam))
    (μ : Fin n → ℤ) (hlam : S7.IsHCParam lam) (hgap : GapAtLeast ε lam h) (hh : 0 < h)
    (hq : 1 ≤ S7.q0 ε) (hμ : S7.IsMu lam μ) :
    ∃ C : ℝ, ∀ g ∈ UJset ε,
      ‖S7.PsiM T μ g‖ ≤ C * frob g ^ (-(h / (8 * Real.sqrt (2 * (S7.q0 ε : ℝ))))) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso; simp [S7.q0, pOf] at hq
    · exact hn
  set r := Real.sqrt (2 * (S7.q0 ε : ℝ)) with hr
  set a := h / (8 * r) with ha
  have hq1 : (1 : ℝ) ≤ S7.q0 ε := by exact_mod_cast hq
  have hr1 : 1 ≤ r := by rw [hr, Real.one_le_sqrt]; linarith
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  refine ⟨Real.exp a * Real.sqrt n ^ a, fun g hg => ?_⟩
  obtain ⟨k, X, hX, rfl⟩ := S7.polar_exists hg
  have hb := S7.psiM_dec T μ hμ hlam hgap hq k hX
  set s := Real.sqrt (S7.hs X) with hsdef
  have hs0 : 0 ≤ S7.hs X := S7.hs_nonnegVG X
  have hs0' : 0 ≤ s := Real.sqrt_nonneg _
  have hss : S7.hs X = s ^ 2 := (Real.sq_sqrt hs0).symm
  set m := min (S7.hs X) (s / r) with hm
  have hkey : a * s - a ≤ (h / 8) * m := by
    have has : a * s = (h / 8) * (s / r) := by rw [ha]; field_simp
    by_cases hc : 1 ≤ s * r
    · have hle : s / r ≤ S7.hs X := by
        rw [hss, div_le_iff₀ (by linarith)]; nlinarith
      rw [hm, min_eq_right hle, ← has]; linarith
    · push_neg at hc
      have hs1 : s < 1 := by nlinarith
      have hm0 : 0 ≤ m := le_min hs0 (div_nonneg hs0' (by linarith))
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ h / 8) hm0]
  have hF := frob_kexp_le ε k X hX
  have hF1 := one_le_frob hn ε _ hg
  have h1 : (Real.sqrt n * Real.exp s) ^ (-a) ≤ frob (S7.toMK k * NormedSpace.exp X) ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hF (by linarith)
  have h2 : (Real.sqrt n * Real.exp s) ^ (-a) = (Real.sqrt n ^ a)⁻¹ * Real.exp (-(a * s)) := by
    rw [Real.mul_rpow hsn.le (Real.exp_pos _).le, ← Real.exp_mul, Real.rpow_neg hsn.le]
    congr 2; ring
  have hpa : 0 < Real.sqrt n ^ a := Real.rpow_pos_of_pos hsn a
  have hm' : -(h / 8) * m = -((h / 8) * m) := by ring
  calc ‖S7.PsiM T μ (S7.toMK k * NormedSpace.exp X)‖ ≤ Real.exp (-(h / 8) * m) := hb
    _ ≤ Real.exp (a - a * s) := Real.exp_le_exp.2 (by rw [hm']; linarith)
    _ = Real.exp a * Real.sqrt n ^ a * ((Real.sqrt n ^ a)⁻¹ * Real.exp (-(a * s))) := by
        rw [sub_eq_add_neg, Real.exp_add]; field_simp
    _ ≤ Real.exp a * Real.sqrt n ^ a * frob (S7.toMK k * NormedSpace.exp X) ^ (-a) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)

theorem conv_dec {n : ℕ} (hn : 0 < n) (ε : Fin n → Bool) (ν : Measure (S7.UJ ε)) [ν.IsHaarMeasure]
    (β : Matrix (Fin n) (Fin n) ℂ → ℂ) (hβ : Continuous β) (hβc : HasCompactSupport β)
    (φ : Matrix (Fin n) (Fin n) ℂ → ℂ) {C0 a : ℝ} (ha : 0 ≤ a)
    (hφ : ∀ g ∈ UJset ε, ‖φ g‖ ≤ C0 * frob g ^ (-a)) :
    ∃ C : ℝ, ∀ g ∈ UJset ε, ‖∫ y, β (S7.toM y) * φ (g * S7.toM y) ∂ν‖ ≤ C * frob g ^ (-a) := by
  classical
  obtain ⟨B, hB⟩ : ∃ B, ∀ x, ‖β x‖ ≤ B := by
    obtain ⟨B, hB⟩ := hβ.norm.bddAbove_range_of_hasCompactSupport hβc.norm
    exact ⟨B, fun x => hB ⟨x, rfl⟩⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hfc : Continuous (frob : Matrix (Fin n) (Fin n) ℂ → ℝ) := Real.continuous_sqrt.comp S7.hs_contVG
  obtain ⟨R0, hR0⟩ : ∃ R0, ∀ x ∈ tsupport β, frob x ≤ R0 := by
    obtain ⟨R0, hR0⟩ := (hβc.isCompact.image_of_continuousOn hfc.continuousOn).bddAbove
    exact ⟨R0, fun x hx => hR0 ⟨x, hx, rfl⟩⟩
  set R := max R0 1 with hRdef
  have hR1 : 1 ≤ R := le_max_right _ _
  set C1 := max C0 0 with hC1
  have hC10 : 0 ≤ C1 := le_max_right _ _
  set K := B * C1 * R ^ a with hK
  have hK0 : 0 ≤ K := by positivity
  set S : Set (S7.UJ ε) := {y | S7.hs (S7.toM y) ≤ R ^ 2} with hSdef
  have hSm : MeasurableSet S :=
    (isClosed_le (S7.hs_contVG.comp (S7.continuous_toM ε)) continuous_const).measurableSet
  have hSf : ν S < ⊤ := S7.ballFiniteVG ε ν _
  refine ⟨K * (ν S).toReal, fun g hg => ?_⟩
  have hg1 := one_le_frob hn ε g hg
  have hpt : ∀ y, ‖β (S7.toM y) * φ (g * S7.toM y)‖ ≤ S.indicator (fun _ => K * frob g ^ (-a)) y := by
    intro y
    by_cases hy : S7.toM y ∈ tsupport β
    · have hyR : frob (S7.toM y) ≤ R := (hR0 _ hy).trans (le_max_left _ _)
      have hyS : y ∈ S := by
        show S7.hs (S7.toM y) ≤ R ^ 2
        have h0 : 0 ≤ frob (S7.toM y) := Real.sqrt_nonneg _
        have : S7.hs (S7.toM y) = frob (S7.toM y) ^ 2 := (Real.sq_sqrt (S7.hs_nonnegVG _)).symm
        rw [this]
        exact pow_le_pow_left₀ h0 hyR 2
      rw [Set.indicator_of_mem hyS, norm_mul]
      have hy1 : S7.toM y ∈ UJset ε := y.2
      have hgy : g * S7.toM y ∈ UJset ε := DecDerivA.inUJ_mul hg hy1
      have hgy1 := one_le_frob hn ε _ hgy
      have hinvM : (S7.toM y)⁻¹ = S7.toM y⁻¹ := Matrix.inv_eq_right_inv (S7.toM_mul_invVG y)
      have hle : frob g ≤ frob (g * S7.toM y) * R := by
        have hinv : g = g * S7.toM y * (S7.toM y)⁻¹ := by
          rw [hinvM, Matrix.mul_assoc, S7.toM_mul_invVG, Matrix.mul_one]
        calc frob g = frob (g * S7.toM y * (S7.toM y)⁻¹) := by rw [← hinv]
          _ ≤ frob (g * S7.toM y) * frob (S7.toM y)⁻¹ := frob_mul_le _ _
          _ = frob (g * S7.toM y) * frob (S7.toM y) := by rw [frob_inv ε _ hy1]
          _ ≤ frob (g * S7.toM y) * R := mul_le_mul_of_nonneg_left hyR (by linarith)
      have hpow : frob (g * S7.toM y) ^ (-a) ≤ R ^ a * frob g ^ (-a) := by
        have h1 : frob g / R ≤ frob (g * S7.toM y) := by
          rw [div_le_iff₀ (by linarith)]; exact hle
        calc frob (g * S7.toM y) ^ (-a) ≤ (frob g / R) ^ (-a) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
          _ = R ^ a * frob g ^ (-a) := by
              rw [Real.div_rpow (by linarith) (by linarith), Real.rpow_neg (by linarith : (0 : ℝ) ≤ R),
                div_inv_eq_mul, mul_comm]
      have hφ' : ‖φ (g * S7.toM y)‖ ≤ C1 * (R ^ a * frob g ^ (-a)) := by
        calc ‖φ (g * S7.toM y)‖ ≤ C0 * frob (g * S7.toM y) ^ (-a) := hφ _ hgy
          _ ≤ C1 * frob (g * S7.toM y) ^ (-a) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
          _ ≤ C1 * (R ^ a * frob g ^ (-a)) := mul_le_mul_of_nonneg_left hpow hC10
      calc ‖β (S7.toM y)‖ * ‖φ (g * S7.toM y)‖ ≤ B * (C1 * (R ^ a * frob g ^ (-a))) :=
            mul_le_mul (hB _) hφ' (norm_nonneg _) hB0
        _ = K * frob g ^ (-a) := by rw [hK]; ring
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => mul_nonneg hK0 (Real.rpow_nonneg (by linarith) _)) y
  have hint : Integrable (S.indicator fun _ => K * frob g ^ (-a)) ν :=
    (integrable_indicator_iff hSm).2 (integrableOn_const hSf.ne)
  calc ‖∫ y, β (S7.toM y) * φ (g * S7.toM y) ∂ν‖ ≤ ∫ y, S.indicator (fun _ => K * frob g ^ (-a)) y ∂ν :=
        norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hpt)
    _ = K * (ν S).toReal * frob g ^ (-a) := by
        rw [integral_indicator_const _ hSm, smul_eq_mul, Measure.real_def]; ring

theorem psiM_funct {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (T : S7.KType ε (lowK ε lam))
    (μ : Fin n → ℤ) (hlam : S7.IsHCParam lam) (hgap : GapAtLeast ε lam h) (hN : hNeed ε < h)
    (hq : 1 ≤ S7.q0 ε) (hμ : S7.IsMu lam μ) :
    ∀ g ∈ UJset ε, ∀ x ∈ UJset ε,
      ((Module.finrank ℂ T.V : ℂ) / ((S7.muK ε Set.univ).toReal : ℂ)) •
          ∫ k, star (LinearMap.trace ℂ T.V (T.op k).toLinearMap) • S7.PsiM T μ (g * S7.toMK k * x) ∂(S7.muK ε) =
        S7.PsiM T μ g * S7.PsiM T μ x := by
  obtain ⟨hP, -⟩ := Base.psiFor n ε lam h T μ hlam hμ hgap hq (DecDerivA.eight_lt_of hN)
  exact psi_funct (DecDerivA.stdGap_of hlam hgap hN) hP

theorem psiM_repro {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (T : S7.KType ε (lowK ε lam))
    (μ : Fin n → ℤ) (hlam : S7.IsHCParam lam) (hgap : GapAtLeast ε lam h) (hN : hNeed ε < h)
    (hq : 1 ≤ S7.q0 ε) (hμ : S7.IsMu lam μ) (ν : Measure (S7.UJ ε)) [ν.IsHaarMeasure] :
    ∃ (β : Matrix (Fin n) (Fin n) ℂ → ℂ) (M : T.V →L[ℂ] T.V),
      ContDiff ℝ (⊤ : ℕ∞) β ∧ HasCompactSupport β ∧
      ∀ g ∈ UJset ε, S7.PsiM T μ g = (∫ y, β (S7.toM y) • S7.PsiM T μ (g * S7.toM y) ∂ν) * M := by
  have hstd := DecDerivA.stdGap_of hlam hgap hN
  have h8 := DecDerivA.eight_lt_of hN
  obtain ⟨hP, hcont⟩ := Base.psiFor n ε lam h T μ hlam hμ hgap hq h8
  have hh : 0 < h := by
    have : 0 ≤ 8 * (n : ℝ) * S7.q0 ε := by positivity
    linarith
  obtain ⟨β, hβ, hβc, hrep⟩ := DecDerivA.reproducing_smooth_compact_kernel hstd hP ν
  refine ⟨β, 1, hβ, hβc, fun g hg => ?_⟩
  rw [mul_one]
  have hb1 : ∀ x ∈ UJset ε, ‖S7.PsiM T μ x‖ ≤ 1 := by
    intro x hx
    obtain ⟨k, X, hX, rfl⟩ := S7.polar_exists hx
    refine (S7.psiM_dec T μ hμ hlam hgap hq k hX).trans ?_
    rw [Real.exp_le_one_iff]
    have : 0 ≤ min (S7.hs X) (Real.sqrt (S7.hs X) / Real.sqrt (2 * S7.q0 ε)) :=
      le_min (S7.hs_nonnegVG X) (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    nlinarith
  have hFc : Continuous (fun y : S7.UJ ε => β (S7.toM y) • S7.PsiM T μ (g * S7.toM y)) :=
    (hβ.continuous.comp (S7.continuous_toM ε)).smul
      (hcont.comp_continuous (continuous_const.mul (S7.continuous_toM ε))
        (fun y => DecDerivA.inUJ_mul hg y.2))
  obtain ⟨B, hB⟩ : ∃ B, ∀ x, ‖β x‖ ≤ B := by
    obtain ⟨B, hB⟩ := hβ.continuous.norm.bddAbove_range_of_hasCompactSupport hβc.norm
    exact ⟨B, fun x => hB ⟨x, rfl⟩⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨R0, hR0⟩ : ∃ R0, ∀ x ∈ tsupport β, S7.hs x ≤ R0 := by
    obtain ⟨R0, hR0⟩ := (hβc.isCompact.image_of_continuousOn S7.hs_contVG.continuousOn).bddAbove
    exact ⟨R0, fun x hx => hR0 ⟨x, hx, rfl⟩⟩
  set S : Set (S7.UJ ε) := {y | S7.hs (S7.toM y) ≤ R0} with hSdef
  have hSm : MeasurableSet S :=
    (isClosed_le (S7.hs_contVG.comp (S7.continuous_toM ε)) continuous_const).measurableSet
  have hSf : ν S < ⊤ := S7.ballFiniteVG ε ν _
  have hFi : Integrable (fun y : S7.UJ ε => β (S7.toM y) • S7.PsiM T μ (g * S7.toM y)) ν := by
    refine Integrable.mono' ((integrable_indicator_iff hSm).2 (integrableOn_const (C := B) hSf.ne))
      hFc.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : S7.toM y ∈ tsupport β
    · rw [Set.indicator_of_mem (show y ∈ S from hR0 _ hy), norm_smul]
      calc ‖β (S7.toM y)‖ * ‖S7.PsiM T μ (g * S7.toM y)‖ ≤ B * 1 :=
            mul_le_mul (hB _) (hb1 _ (DecDerivA.inUJ_mul hg y.2)) (norm_nonneg _) hB0
        _ = B := mul_one B
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_smul, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => hB0) y
  refine ContinuousLinearMap.ext fun v₁ => ext_inner_left ℂ fun v₂ => ?_
  rw [hrep g hg v₁ v₂, ContinuousLinearMap.integral_apply hFi v₁,
    ← integral_inner (hFi.apply_continuousLinearMap v₁) v₂]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [_root_.smul_apply, inner_smul_right]

theorem eword_repro {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (μ : Fin n → ℤ) (ν : Measure (S7.UJ ε)) [ν.IsHaarMeasure]
    (hcont : ContinuousOn (S7.PsiM T μ) (UJset ε)) (β : Matrix (Fin n) (Fin n) ℂ → ℂ) (M : T.V →L[ℂ] T.V) (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β)
    (hrep : ∀ g ∈ UJset ε, S7.PsiM T μ g = (∫ y, β (S7.toM y) • S7.PsiM T μ (g * S7.toM y) ∂ν) * M)
    (w : List (Fin n × Fin n)) (v₁ v₂ : T.V) :
    ∃ βw : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) βw ∧ HasCompactSupport βw ∧
      ∀ g ∈ UJset ε, Formalism.REAL.Eword ε w (fun y => ⟪v₂, S7.PsiM T μ y v₁⟫_ℂ) g =
        ∫ y, βw (S7.toM y) * ⟪v₂, S7.PsiM T μ (g * S7.toM y) (M v₁)⟫_ℂ ∂ν :=
  DecRepro.eword_repro ε lam T μ ν hcont β M hβ hβc hrep w v₁ v₂

theorem decDeriv : DecDerivStatement := by
  intro n ε lam h T μ hlam hgap hN hq hμ w v₁ v₂
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso; simp [S7.q0, pOf] at hq
    · exact hn
  have hstd := DecDerivA.stdGap_of hlam hgap hN
  have h8 := DecDerivA.eight_lt_of hN
  obtain ⟨hP, hcont⟩ := Base.psiFor n ε lam h T μ hlam hμ hgap hq h8
  have hh : 0 < h := by
    have : 0 ≤ 8 * (n : ℝ) * S7.q0 ε := by positivity
    linarith
  haveI := S7.haar_isHaar ε
  obtain ⟨β, hβ, hβc, hrep⟩ := DecDerivA.reproducing_smooth_compact_kernel hstd hP (Measure.haar : Measure (S7.UJ ε))
  have hφ : ContinuousOn (fun y => ⟪v₂, S7.PsiM T μ y v₁⟫_ℂ) (UJset ε) :=
    continuousOn_const.inner (hcont.clm_apply continuousOn_const)
  obtain ⟨βw, hβw, hβwc, hw⟩ :=
    DecRepro.eword_conv (Measure.haar : Measure (S7.UJ ε)) hβ hβc hφ (fun g hg => hrep g hg v₁ v₂) w
  obtain ⟨C0, hC0⟩ := psiM_frob_dec ε lam h T μ hlam hgap hh hq hμ
  have ha : 0 ≤ h / (8 * Real.sqrt (2 * (S7.q0 ε : ℝ))) := by positivity
  obtain ⟨C, hC⟩ := conv_dec hn ε (Measure.haar : Measure (S7.UJ ε)) βw hβw.continuous hβwc
    (fun y => ⟪v₂, S7.PsiM T μ y v₁⟫_ℂ) (C0 := ‖v₂‖ * ‖v₁‖ * C0) ha (fun g hg => by
      calc ‖⟪v₂, S7.PsiM T μ g v₁⟫_ℂ‖ ≤ ‖v₂‖ * ‖S7.PsiM T μ g v₁‖ := norm_inner_le_norm _ _
        _ ≤ ‖v₂‖ * (‖S7.PsiM T μ g‖ * ‖v₁‖) :=
            mul_le_mul_of_nonneg_left ((S7.PsiM T μ g).le_opNorm v₁) (norm_nonneg _)
        _ ≤ ‖v₂‖ * ((C0 * frob g ^ (-(h / (8 * Real.sqrt (2 * (S7.q0 ε : ℝ)))))) * ‖v₁‖) := by
            gcongr
            exact hC0 g hg
        _ = _ := by ring)
  exact ⟨C, fun g hg => by rw [hw g hg]; exact hC g hg⟩

end ReciprocityTheory.ChartRestriction.DS.Lap.S0.DecDeriv
