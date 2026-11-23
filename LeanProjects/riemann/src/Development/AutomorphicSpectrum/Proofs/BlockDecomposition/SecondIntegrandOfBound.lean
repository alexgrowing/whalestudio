import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.SmoothMajorants.Bounds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRightTranslate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VolumeSingularMatricesZero

noncomputable section

open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.B

namespace GlobalTheory.CompanionTheory.SecJC

theorem norm_ph (n : ℤ) {z : ℂ} (hz : z ≠ 0) : ‖ph n z‖ = 1 := by
  have h : ‖z / (‖z‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr hz)]
  unfold ph
  rw [norm_zpow, h, _root_.one_zpow]

theorem measurable_ph (n : ℤ) : Measurable (ph n) := by
  have h : Measurable (fun z : ℂ => z / (‖z‖ : ℂ)) :=
    measurable_id.div (Complex.measurable_ofReal.comp measurable_norm)
  cases n with
  | ofNat m =>
    have e : ph (Int.ofNat m) = fun z : ℂ => (z / (‖z‖ : ℂ)) ^ m := by
      funext z
      exact zpow_natCast _ m
    rw [e]
    exact h.pow_const m
  | negSucc m =>
    have e : ph (Int.negSucc m) = fun z : ℂ => ((z / (‖z‖ : ℂ)) ^ (m + 1))⁻¹ := by
      funext z
      exact zpow_negSucc _ m
    rw [e]
    exact (h.pow_const (m + 1)).inv

theorem continuous_psiC : Continuous psiC := by
  unfold psiC
  fun_prop

theorem continuous_blk : Continuous blk := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [blk] <;> fun_prop

theorem continuous_det : Continuous (fun h : M22 => (Matrix.of h).det) :=
  Continuous.matrix_det (continuous_id : Continuous fun h : M22 => h)

theorem measurable_rowv :
    Measurable (fun q : (M22 × ℂ) × ((Fin 2 → ℂ) × ℂ) => rowv q.1.2 q.2.2 (Matrix.of q.1.1)) := by
  refine measurable_pi_iff.mpr fun j => ?_
  have hd : Measurable (fun q : (M22 × ℂ) × ((Fin 2 → ℂ) × ℂ) => ((Matrix.of q.1.1).det)⁻¹) :=
    (continuous_det.measurable.comp (measurable_fst.comp measurable_fst)).inv
  have he : ∀ (a b : Fin 2), Measurable (fun q : (M22 × ℂ) × ((Fin 2 → ℂ) × ℂ) => q.1.1 a b) := by
    intro a b
    fun_prop
  have ht : Measurable (fun q : (M22 × ℂ) × ((Fin 2 → ℂ) × ℂ) => q.1.2) := by fun_prop
  have hy : Measurable (fun q : (M22 × ℂ) × ((Fin 2 → ℂ) × ℂ) => q.2.2) := by fun_prop
  simp only [rowv, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]
  fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> fun_prop

theorem measurable_inn (Ψ : Sw) (g : GL (Fin 3) ℂ) :
    Measurable (fun p : M22 × ℂ => inn Ψ g (Matrix.of p.1) p.2) := by
  have hA : Continuous (fun q : (M22 × ℂ) × ((Fin 2 → ℂ) × ℂ) =>
      (Matrix.of.symm (Matrix.of q.1.1 * blk q.2.1 * (g : Matrix (Fin 3) (Fin 3) ℂ)) : M23)) := by
    have h1 : Continuous (fun q : (M22 × ℂ) × ((Fin 2 → ℂ) × ℂ) => (Matrix.of q.1.1 : Matrix (Fin 2) (Fin 2) ℂ)) :=
      continuous_fst.comp continuous_fst
    have h2 : Continuous (fun q : (M22 × ℂ) × ((Fin 2 → ℂ) × ℂ) => blk q.2.1) :=
      continuous_blk.comp (continuous_fst.comp continuous_snd)
    exact (h1.matrix_mul h2).matrix_mul continuous_const
  have hF : Measurable (fun q : (M22 × ℂ) × ((Fin 2 → ℂ) × ℂ) =>
      Ψ (Matrix.of.symm (Matrix.of q.1.1 * blk q.2.1 * (g : Matrix (Fin 3) (Fin 3) ℂ)),
        rowv q.1.2 q.2.2 (Matrix.of q.1.1)) * psiC (-(q.2.1 1)) * psiC (-q.2.2)) := by
    refine ((Ψ.continuous.measurable.comp (hA.measurable.prodMk measurable_rowv)).mul ?_).mul ?_
    · exact (continuous_psiC.comp (by fun_prop)).measurable
    · exact (continuous_psiC.comp (by fun_prop)).measurable
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

theorem measurable_secI (k : ℕ) (Ψ : Sw) (g : GL (Fin 3) ℂ) : Measurable (secI k Ψ g) := by
  have hd : Measurable (fun p : M22 × ℂ => (Matrix.of p.1).det) :=
    continuous_det.measurable.comp measurable_fst
  unfold secI
  refine (((measurable_inn Ψ g).mul ((measurable_ph _).comp measurable_snd)).mul
    ((measurable_ph _).comp hd)).mul ?_
  exact Complex.measurable_ofReal.comp ((measurable_norm.comp hd).pow_const _)

theorem inn_eq_innB (Ψ : Sw) (g : GL (Fin 3) ℂ) (Φ : Sw)
    (hΦ : ∀ (X : M23) (q : Fin 2 → ℂ), Φ (X, q) =
      Ψ (Matrix.of.symm (Matrix.of X * (g : Matrix (Fin 3) (Fin 3) ℂ)), q))
    (h : M22) (t : ℂ) : inn Ψ g (Matrix.of h) t = innB Φ h t 1 1 := by
  unfold inn innB
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp [hΦ]

theorem ae_good : ∀ᵐ p : M22 × ℂ, (Matrix.of p.1).det ≠ 0 ∧ p.2 ≠ 0 := by
  have h1 : ∀ᵐ h : M22, (Matrix.of h).det ≠ 0 := by
    rw [ae_iff]
    simpa using GlobalTheory.CompanionTheory.DetC.volume_det_fin_two_complex_eq_zero
  have h2 : ∀ᵐ t : ℂ, t ≠ 0 := by
    rw [ae_iff]
    simp
  have h1' := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure M22)) (ν := (volume : Measure ℂ))).ae h1
  have h2' := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure M22)) (ν := (volume : Measure ℂ))).ae h2
  rw [← Measure.volume_eq_prod] at h1' h2'
  filter_upwards [h1', h2'] with p a b using ⟨a, b⟩

theorem main : IbpBound → MajScaled → SecJ := by
  intro hI hM k _ Ψ g
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.CompanionTheory.SchwartzTranslateC.exists_rightTranslate g Ψ
  obtain ⟨N, hN⟩ := hM 1 one_pos
  obtain ⟨C₁, hC₁⟩ := hN N le_rfl
  have hint := (hC₁ 1 1 one_ne_zero one_ne_zero).1
  obtain ⟨C, hC⟩ := hI N
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ n ≤ 2 * N, ∀ X : E5,
      (1 + ‖X‖) ^ (2 * N + 20) * ‖iteratedFDeriv ℝ n Φ X‖ ≤ B :=
    ⟨_, fun n hn X => SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (2 * N + 20, 2 * N)) le_rfl hn Φ X⟩
  refine Integrable.mono' (hint.const_mul (C * B)) (measurable_secI k Ψ g).aestronglyMeasurable ?_
  filter_upwards [ae_good] with p hp
  obtain ⟨hd, ht⟩ := hp
  have hbd : ‖innB Φ p.1 p.2 1 1‖ ≤ C * B * jm N p.1 p.2 1 1 :=
    hC Φ B (Φ.smooth ⊤) hB p.1 p.2 1 1 hd ht one_ne_zero
  have hn : ‖(((‖(Matrix.of p.1).det‖ ^ (-(2 : ℝ)) : ℝ)) : ℂ)‖ = (‖(Matrix.of p.1).det‖ ^ 2)⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.rpow_neg (norm_nonneg _)]
    norm_cast
  have hD : 0 ≤ (‖(Matrix.of p.1).det‖ ^ 2)⁻¹ := by positivity
  unfold secI
  rw [norm_mul, norm_mul, norm_mul, norm_ph _ ht, norm_ph _ hd, hn, mul_one, mul_one,
    inn_eq_innB Ψ g Φ hΦ]
  calc ‖innB Φ p.1 p.2 1 1‖ * (‖(Matrix.of p.1).det‖ ^ 2)⁻¹
      ≤ C * B * jm N p.1 p.2 1 1 * (‖(Matrix.of p.1).det‖ ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hbd hD
    _ = C * B * ((‖(Matrix.of p.1).det‖ ^ 2)⁻¹ * jm N p.1 p.2 1 1) := by ring

end GlobalTheory.CompanionTheory.SecJC
