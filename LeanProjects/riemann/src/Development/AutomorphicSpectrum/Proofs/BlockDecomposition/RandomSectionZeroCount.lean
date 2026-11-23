import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianDetLeviIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexHessianLogFubiniStudyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexHessianLogDehomogeniseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableZeroCountStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChangeVariablesZeroCountStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralSplitColumnStatement
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton

theorem measurable_gW (d : ℕ) (α : Type) [Fintype α] : Measurable (gW d α) := by
  have hc : Continuous fun C : Fin d → α → ℂ => Real.exp (-∑ k, ∑ j, ‖C k j‖ ^ 2) := by
    fun_prop
  exact ENNReal.measurable_ofReal.comp hc.measurable

theorem gW_ne_top (d : ℕ) (α : Type) [Fintype α] (C : Fin d → α → ℂ) : gW d α C ≠ ∞ :=
  ENNReal.ofReal_ne_top

theorem measurable_gauss (d : ℕ) :
    Measurable fun c : Fin d → ℂ => ENNReal.ofReal (Real.exp (-∑ k, ‖c k‖ ^ 2)) := by
  have hc : Continuous fun c : Fin d → ℂ => Real.exp (-∑ k, ‖c k‖ ^ 2) := by
    fun_prop
  exact ENNReal.measurable_ofReal.comp hc.measurable

theorem gW_joinCol {d : ℕ} {α : Type} [Fintype α] [DecidableEq α] (j₀ : α) (c : Fin d → ℂ)
    (C : Fin d → {j : α // j ≠ j₀} → ℂ) :
    gW d α (joinCol j₀ c C) =
      gW d {j : α // j ≠ j₀} C * ENNReal.ofReal (Real.exp (-∑ k, ‖c k‖ ^ 2)) := by
  unfold gW
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  rw [← neg_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j₀, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp [joinCol, j.2]
  · simp [joinCol]

theorem joinCol_zero_iff {X : Type} {d : ℕ} {α : Type} [Fintype α] [DecidableEq α] (j₀ : α)
    (c : Fin d → ℂ) (C : Fin d → {j : α // j ≠ j₀} → ℂ) (b : α → X → ℂ) (z : X)
    (hz : b j₀ z ≠ 0) :
    (∀ k, ∑ j, joinCol j₀ c C k j * b j z = 0) ↔
      ∀ k, c k + ∑ j : {j : α // j ≠ j₀}, C k j * (b j.1 z / b j₀ z) = 0 := by
  refine forall_congr' fun k => ?_
  have h : ∑ j, joinCol j₀ c C k j * b j z =
      b j₀ z * (c k + ∑ j : {j : α // j ≠ j₀}, C k j * (b j.1 z / b j₀ z)) := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ j₀, mul_add, Finset.mul_sum]
    congr 1
    · simp [joinCol, mul_comm]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [joinCol, j.2, dite_false]
      field_simp
  rw [h, mul_eq_zero]
  simp [hz]

theorem continuous_kernel (d : ℕ) (β : Type) [Fintype β] :
    Continuous fun q : (Fin d → β → ℂ) × ((β → ℂ) × (β → Fin d → ℂ)) =>
      Real.exp (-∑ k, ‖∑ j, q.1 k j * q.2.1 j‖ ^ 2) *
        ‖(Matrix.of q.1 * (Matrix.of q.2.2 : Matrix β (Fin d) ℂ)).det‖ ^ 2 := by
  have h1 : Continuous fun q : (Fin d → β → ℂ) × ((β → ℂ) × (β → Fin d → ℂ)) =>
      (Matrix.of q.1 : Matrix (Fin d) β ℂ) := continuous_fst
  have h2 : Continuous fun q : (Fin d → β → ℂ) × ((β → ℂ) × (β → Fin d → ℂ)) =>
      (Matrix.of q.2.2 : Matrix β (Fin d) ℂ) := continuous_snd.comp continuous_snd
  have h3 : Continuous fun q : (Fin d → β → ℂ) × ((β → ℂ) × (β → Fin d → ℂ)) =>
      (Matrix.of q.1 * (Matrix.of q.2.2 : Matrix β (Fin d) ℂ)).det :=
    (h1.matrix_mul h2).matrix_det
  have h4 : Continuous fun q : (Fin d → β → ℂ) × ((β → ℂ) × (β → Fin d → ℂ)) =>
      Real.exp (-∑ k, ‖∑ j, q.1 k j * q.2.1 j‖ ^ 2) := by
    refine Real.continuous_exp.comp (continuous_neg.comp ?_)
    refine continuous_finset_sum _ fun k _ => (Continuous.norm ?_).pow 2
    refine continuous_finset_sum _ fun j _ => Continuous.mul ?_ ?_
    · exact (continuous_apply j).comp ((continuous_apply k).comp continuous_fst)
    · exact (continuous_apply j).comp (continuous_fst.comp continuous_snd)
  exact h4.mul (h3.norm.pow 2)

theorem measurable_kernel {X : Type} [MeasurableSpace X] (d : ℕ) (β : Type) [Fintype β]
    (g : β → X → ℂ) (F : β → Fin d → X → ℂ) (hg : ∀ j, Measurable (g j))
    (hF : ∀ j a, Measurable (F j a)) :
    Measurable fun p : (Fin d → β → ℂ) × X =>
      gW d β p.1 * ENNReal.ofReal (Real.exp (-∑ k, ‖∑ j, p.1 k j * g j p.2‖ ^ 2) *
        ‖(Matrix.of p.1 * (Matrix.of fun j a => F j a p.2 : Matrix β (Fin d) ℂ)).det‖ ^ 2) := by
  have hm : Measurable fun p : (Fin d → β → ℂ) × X =>
      ((p.1, (fun j => g j p.2), (fun j a => F j a p.2)) :
        (Fin d → β → ℂ) × ((β → ℂ) × (β → Fin d → ℂ))) := by
    refine measurable_fst.prodMk (Measurable.prodMk ?_ ?_)
    · exact measurable_pi_lambda _ fun j => (hg j).comp measurable_snd
    · exact measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun a =>
        (hF j a).comp measurable_snd
  have hq := (continuous_kernel d β).measurable.comp hm
  exact ((measurable_gW d β).comp measurable_fst).mul (ENNReal.measurable_ofReal.comp hq)

theorem differentiableOn_quot {d : ℕ} {α : Type} (U : Set (V d)) (b : α → V d → ℂ)
    (hb : ∀ j, DifferentiableOn ℂ (b j) U) (j₀ : α) (hne : ∀ z ∈ U, b j₀ z ≠ 0) (j : α) :
    DifferentiableOn ℂ (fun v => b j v / b j₀ v) U := by
  have h : DifferentiableOn ℂ (fun v => b j v * (b j₀ v)⁻¹) U := (hb j).mul ((hb j₀).inv hne)
  simpa only [div_eq_mul_inv] using h

theorem inner_integral (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (U A : Set (V d))
    (b : α → V d → ℂ) (hU : IsOpen U) (hb : ∀ j, DifferentiableOn ℂ (b j) U)
    (hne : ∀ z ∈ U, b j₀ z ≠ 0) (hAU : A ⊆ U) (hAm : MeasurableSet A)
    (g : {j : α // j ≠ j₀} → V d → ℂ) (hgA : ∀ j, ∀ z ∈ A, g j z = b j.1 z / b j₀ z)
    (C : Fin d → {j : α // j ≠ j₀} → ℂ) :
    ∫⁻ c : Fin d → ℂ, gW d α (joinCol j₀ c C) * zeroCnt d A b (joinCol j₀ c C) =
      ∫⁻ z in A, gW d {j : α // j ≠ j₀} C *
        ENNReal.ofReal (Real.exp (-∑ k, ‖∑ j, C k j * g j z‖ ^ 2) *
          ‖(Matrix.of C * (Matrix.of fun j a =>
            fderiv ℂ (fun v => b (j : {j : α // j ≠ j₀}).1 v / b j₀ v) z
              (EuclideanSpace.single a 1) : Matrix {j : α // j ≠ j₀} (Fin d) ℂ)).det‖ ^ 2) := by
  have hf : ∀ j : {j : α // j ≠ j₀}, DifferentiableOn ℂ (fun v => b j.1 v / b j₀ v) U :=
    fun j => differentiableOn_quot U b hb j₀ hne j.1
  have e1 : ∀ c : Fin d → ℂ, gW d α (joinCol j₀ c C) * zeroCnt d A b (joinCol j₀ c C) =
      gW d {j : α // j ≠ j₀} C * (ENNReal.ofReal (Real.exp (-∑ k, ‖c k‖ ^ 2)) *
        (({z ∈ A | ∀ k, c k + ∑ j : {j : α // j ≠ j₀}, C k j * (b j.1 z / b j₀ z) = 0}.encard :
          ℕ∞) : ℝ≥0∞)) := by
    intro c
    have hs : {z ∈ A | ∀ k, ∑ j, joinCol j₀ c C k j * b j z = 0} =
        {z ∈ A | ∀ k, c k + ∑ j : {j : α // j ≠ j₀}, C k j * (b j.1 z / b j₀ z) = 0} := by
      ext z
      simp only [Set.mem_setOf_eq]
      refine and_congr_right fun hz => ?_
      exact joinCol_zero_iff j₀ c C b z (hne z (hAU hz))
    rw [gW_joinCol, mul_assoc]
    unfold zeroCnt
    rw [hs]
  simp_rw [e1]
  rw [lintegral_const_mul' _ _ (gW_ne_top d _ C),
    GlobalTheory.T.change_variables_zero_count d {j : α // j ≠ j₀} U A (fun j v => b j.1 v / b j₀ v) C
      (fun c => ENNReal.ofReal (Real.exp (-∑ k, ‖c k‖ ^ 2))) hU hf hAU hAm (measurable_gauss d),
    ← lintegral_const_mul' _ _ (gW_ne_top d _ C)]
  refine setLIntegral_congr_fun hAm fun z hz => ?_
  simp only [norm_neg]
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp only [hgA _ z hz]

theorem const_arith (d m n : ℕ) (hn : n = m + 1) (x : ℝ) :
    ENNReal.ofReal (Real.pi ^ (d * m) * (d.factorial : ℝ) * x) =
      ENNReal.ofReal (Real.pi ^ (d * n)) *
        ENNReal.ofReal ((d.factorial : ℝ) / Real.pi ^ d * x) := by
  rw [← ENNReal.ofReal_mul (pow_nonneg Real.pi_pos.le _)]
  congr 1
  subst hn
  have hp : (Real.pi ^ d) ≠ 0 := pow_ne_zero _ Real.pi_pos.ne'
  rw [Nat.mul_succ, pow_add]
  field_simp

theorem crofton_local : ∀ (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (U A : Set (V d)) (b : α → V d → ℂ), IsOpen U → (∀ j, DifferentiableOn ℂ (b j) U) → (∀ z ∈ U, b j₀ z ≠ 0) → A ⊆ U → IsSigmaCompact A → ∫⁻ C : Fin d → α → ℂ, gW d α C * zeroCnt d A b C = ENNReal.ofReal (Real.pi ^ (d * Fintype.card α)) * ∫⁻ z in A, ENNReal.ofReal ((d.factorial : ℝ) / Real.pi ^ d * (cHess d (fun v => ((Real.log (∑ j, ‖b j v‖ ^ 2) : ℝ) : ℂ)) z).det.re) := by
  intro d α _ _ j₀ U A b hU hb hne hAU hA
  classical
  have hAm : MeasurableSet A := by
    obtain ⟨K, hK, hKA⟩ := hA
    rw [← hKA]
    exact MeasurableSet.iUnion fun n => (hK n).measurableSet
  have hΦ : Measurable fun C : Fin d → α → ℂ => gW d α C * zeroCnt d A b C :=
    (measurable_gW d α).mul (GlobalTheory.T.measurable_zero_count d α U A b (fun j => (hb j).continuousOn) hAU hA)
  have hf : ∀ j : {j : α // j ≠ j₀}, DifferentiableOn ℂ (fun v => b j.1 v / b j₀ v) U :=
    fun j => differentiableOn_quot U b hb j₀ hne j.1
  obtain ⟨g, hg, hgA⟩ : ∃ g : {j : α // j ≠ j₀} → V d → ℂ, (∀ j, Measurable (g j)) ∧
      ∀ j, ∀ z ∈ A, g j z = b j.1 z / b j₀ z := by
    refine ⟨fun j => U.piecewise (fun v => b j.1 v / b j₀ v) (fun _ => 0), fun j => ?_,
      fun j z hz => by simp [Set.piecewise, hAU hz]⟩
    exact (hf j).continuousOn.measurable_piecewise continuousOn_const hU.measurableSet
  have hF : ∀ (j : {j : α // j ≠ j₀}) (a : Fin d), Measurable fun z =>
      fderiv ℂ (fun v => b j.1 v / b j₀ v) z (EuclideanSpace.single a 1) :=
    fun j a => measurable_fderiv_apply_const ℂ _ _
  have hK := measurable_kernel d {j : α // j ≠ j₀} g _ hg hF
  rw [GlobalTheory.T.lintegral_split_column d α j₀ _ hΦ]
  simp_rw [inner_integral d α j₀ U A b hU hb hne hAU hAm g hgA]
  rw [lintegral_lintegral_swap (ν := volume.restrict A) hK.aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun hAm fun z hz => ?_
  have hcard : Fintype.card α = Fintype.card {j : α // j ≠ j₀} + 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    have : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨j₀⟩
    omega
  have h1 := GlobalTheory.T.gaussian_det_levi_integral d {j : α // j ≠ j₀} (fun j => b j.1 z / b j₀ z)
    (Matrix.of fun j a => fderiv ℂ (fun v => b (j : {j : α // j ≠ j₀}).1 v / b j₀ v) z
      (EuclideanSpace.single a 1))
  rw [GlobalTheory.T.complex_hessian_log_dehomogenise d α j₀ U b hU hb hne z (hAU hz),
    GlobalTheory.T.complex_hessian_log_fubini_study d {j : α // j ≠ j₀} U (fun j v => b j.1 v / b j₀ v) hU hf z (hAU hz),
    ← const_arith d _ _ hcard, ← h1]
  simp only [hgA _ z hz]

end GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton
