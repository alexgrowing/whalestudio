import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureTensorDecompositionLocal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalEquationThirdHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalEquationNinthHypothesis
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.PFTBound

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem exists_entry_bound {s : Set (Matrix (Fin 2) (Fin 2) F)} (hs : IsCompact s) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ A ∈ s, ∀ i j, (modulus (A i j) : ℝ) ≤ R := by
  have hc : Continuous (fun A : Matrix (Fin 2) (Fin 2) F =>
      ∑ i, ∑ j, (modulus (A i j) : ℝ)) := by
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact NNReal.continuous_coe.comp (continuous_modulus.comp (continuous_id.matrix_elem i j))
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun A hA i j => ?_⟩
  have h1 : (modulus (A i j) : ℝ) ≤ ∑ j, (modulus (A i j) : ℝ) :=
    Finset.single_le_sum (f := fun j => (modulus (A i j) : ℝ))
      (fun _ _ => NNReal.coe_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j, (modulus (A i j) : ℝ) ≤ ∑ i, ∑ j, (modulus (A i j) : ℝ) :=
    Finset.single_le_sum (f := fun i => ∑ j, (modulus (A i j) : ℝ))
      (fun _ _ => Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _) (Finset.mem_univ i)
  have h3 := hC A hA
  exact (h1.trans h2).trans ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans
    (h3.trans (le_max_left _ _))))

theorem exists_mx_bound {s : Set (Fin 2 → F)} (hs : IsCompact s) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ ξ ∈ s, mx ξ ≤ R := by
  have hc : Continuous (fun ξ : Fin 2 → F => mx ξ) := by
    unfold mx
    exact (NNReal.continuous_coe.comp (continuous_modulus.comp (continuous_apply 0))).max
      (NNReal.continuous_coe.comp (continuous_modulus.comp (continuous_apply 1)))
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun ξ hξ =>
    (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans ((hC ξ hξ).trans (le_max_left _ _)))⟩

theorem ftN_mem (ψ : AddChar F Circle) (hψ : IsStd ψ) {φ : (Fin 2 → F) → ℂ}
    (hφ : φ ∈ GodementSectionLocal.schwartzBruhat2 F) :
    ftN ψ φ ∈ GodementSectionLocal.schwartzBruhat2 F := by
  have h := (GlobalTheory.CompanionTheory.FourierPlane.fourier_inversion_plane_explicit F ψ hψ φ hφ).1
  have e : ftN ψ φ = fun ξ : Fin 2 → F =>
      ∫ y, φ y * (ψ (-(ξ 0 * y 0 + ξ 1 * y 1)) : ℂ) ∂LFS.vol2 ψ := by
    funext ξ
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [mul_comm (x 0), mul_comm (x 1)]
  rw [e]
  exact h

end D

theorem pFT_continuous_bounded : ForS fun F _ _ _ _ _ _ ψ => ∀ Φ ∈ LFS.SB F,
    Continuous (fun q : Matrix (Fin 2) (Fin 2) F × (Fin 2 → F) => pFT ψ Φ q.1 q.2) ∧
    ∃ C R : ℝ, 0 ≤ C ∧ ∀ A ξ, ‖pFT ψ Φ A ξ‖ ≤ C ∧
      (pFT ψ Φ A ξ ≠ 0 → (∀ i j, (modulus (A i j) : ℝ) ≤ R) ∧ mx ξ ≤ R) := by
  intro F _ _ _ _ _ _ ψ hψ Φ hΦ
  obtain ⟨n, Φ₁, Φ₂, h₁, h₂, hs⟩ := GlobalTheory.CompanionTheory.PureTensor.k2pt F ψ hψ Φ hΦ
  have hsum : ∀ A ξ, pFT ψ Φ A ξ = ∑ i, Φ₁ i A * ftN ψ (Φ₂ i) ξ :=
    (GlobalTheory.CompanionTheory.PureTensorFourier.a3 F ψ hψ n Φ Φ₁ Φ₂ h₁ h₂ hs).1
  have hg : ∀ i, IsLocallyConstant (ftN ψ (Φ₂ i)) ∧ HasCompactSupport (ftN ψ (Φ₂ i)) :=
    fun i => GodementSectionLocal.mem_schwartzBruhat2.1 (ftN_mem ψ hψ (h₂ i))
  have hc₁ : ∀ i, Continuous (Φ₁ i) := fun i => (h₁ i).1.continuous
  have hc₂ : ∀ i, Continuous (ftN ψ (Φ₂ i)) := fun i => (hg i).1.continuous
  refine ⟨?_, ?_⟩
  · have e : (fun q : Matrix (Fin 2) (Fin 2) F × (Fin 2 → F) => pFT ψ Φ q.1 q.2) =
        fun q => ∑ i, Φ₁ i q.1 * ftN ψ (Φ₂ i) q.2 := funext fun q => hsum q.1 q.2
    rw [e]
    exact continuous_finset_sum _ fun i _ =>
      ((hc₁ i).comp continuous_fst).mul ((hc₂ i).comp continuous_snd)
  · choose B₁ hB₁ using fun i => (hc₁ i).bounded_above_of_compact_support (h₁ i).2
    choose B₂ hB₂ using fun i => (hc₂ i).bounded_above_of_compact_support (hg i).2
    choose R₁ hR₁ hR₁' using fun i => exists_entry_bound (h₁ i).2.isCompact
    choose R₂ hR₂ hR₂' using fun i => exists_mx_bound (hg i).2.isCompact
    have hB₁0 : ∀ i, 0 ≤ B₁ i := fun i => (norm_nonneg _).trans (hB₁ i 0)
    have hB₂0 : ∀ i, 0 ≤ B₂ i := fun i => (norm_nonneg _).trans (hB₂ i 0)
    refine ⟨∑ i, B₁ i * B₂ i, ∑ i, (R₁ i + R₂ i),
      Finset.sum_nonneg fun i _ => mul_nonneg (hB₁0 i) (hB₂0 i), fun A ξ => ⟨?_, fun hne => ?_⟩⟩
    · rw [hsum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul]
      exact mul_le_mul (hB₁ i A) (hB₂ i ξ) (norm_nonneg _) (hB₁0 i)
    · rw [hsum] at hne
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      have hA : Φ₁ i A ≠ 0 := left_ne_zero_of_mul hi
      have hξ : ftN ψ (Φ₂ i) ξ ≠ 0 := right_ne_zero_of_mul hi
      have hle : R₁ i + R₂ i ≤ ∑ i, (R₁ i + R₂ i) :=
        Finset.single_le_sum (f := fun i => R₁ i + R₂ i)
          (fun i _ => add_nonneg (hR₁ i) (hR₂ i)) (Finset.mem_univ i)
      refine ⟨fun a b => ?_, ?_⟩
      · have := hR₁' i A (subset_tsupport _ hA) a b
        linarith [hR₂ i]
      · have := hR₂' i ξ (subset_tsupport _ hξ)
        linarith [hR₁ i]

end GlobalTheory.CompanionTheory.PFTBound
