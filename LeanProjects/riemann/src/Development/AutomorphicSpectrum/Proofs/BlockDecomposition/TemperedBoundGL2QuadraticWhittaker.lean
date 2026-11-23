import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSmoothCharCompNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WcEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerBoundQuadraticExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerSupportQuadraticExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilCharacterTwistNontrivialGaloisStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerGaloisConjugateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerNontrivialGaloisIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactTranslateEntriesBoundedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenNormImageUnitsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormImageNeighbourhoodEventuallyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerContinuityQuadraticExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerMeasureIndependenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerNonvanishingCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerMeasurabilityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerGaloisInvarianceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerIntegrableQuadraticStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerContinuousQuadraticStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerSupportBoundQuadraticStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerCentralTwistStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerNontrivialCharacterExtensionStatement
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.WcB

section Meas

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E]
  [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)]

theorem measurable_indicator_of_continuousOn {f : GL (Fin 2) F → ℂ} {s : Set (GL (Fin 2) F)}
    (hf : ContinuousOn f s) (hs : MeasurableSet s) : Measurable (s.indicator f) := by
  classical
  have h := ContinuousOn.measurable_piecewise (f := f) (g := fun _ => (0 : ℂ)) hf
    continuousOn_const hs
  have e : s.piecewise f (fun _ => (0 : ℂ)) = s.indicator f := by
    ext g
    by_cases hg : g ∈ s <;> simp [Set.piecewise, Set.indicator, hg]
  rwa [e] at h

theorem measurable_Wc (χ : AddChar F Circle) (hχ : Continuous χ) (hal : Continuous (algebraMap F E))
    (σ : E ≃ₐ[F] E) (hσ : σ ≠ AlgEquiv.refl) (μ : Measure E) [μ.IsAddHaarMeasure] (lam : ℂ)
    (c : Eˣ →* ℂˣ) (hc : IsUnit1 c) (Φ : E → ℂ) (hΦ : Φ ∈ GL2LocalData.SBc F E c) :
    Measurable (GL2LocalData.Wc χ σ μ lam c Φ) := by
  set Gp : Set (GL (Fin 2) F) := {g | ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det} with hGp
  have hdet : Continuous fun g : GL (Fin 2) F => (g.val).det :=
    Continuous.matrix_det Units.continuous_val
  have hent : Continuous fun g : GL (Fin 2) F => g.val 1 0 :=
    (continuous_id.matrix_elem 1 0).comp Units.continuous_val
  have hGo : IsOpen Gp := (GlobalTheory.T.isOpen_norm_image_units F E).1.preimage hdet
  have hA0 : IsClosed {g : GL (Fin 2) F | g.val 1 0 = 0} := isClosed_eq hent continuous_const
  have hA1 : IsOpen {g : GL (Fin 2) F | g.val 1 0 ≠ 0} := isOpen_ne_fun hent continuous_const
  have c1 : ContinuousOn (GL2LocalData.Wc χ σ μ lam c Φ) ({g : GL (Fin 2) F | g.val 1 0 ≠ 0} ∩ Gp) :=
    GlobalTheory.T.weil_whittaker_central_twist F E χ σ μ lam c Φ hΦ _
      (GlobalTheory.T.weil_whittaker_continuous_quadratic F E χ hχ hal σ hσ μ lam c hc Φ hΦ.1 hΦ.2.1)
  have c0 : ContinuousOn (GL2LocalData.Wc χ σ μ lam c Φ) ({g : GL (Fin 2) F | g.val 1 0 = 0} ∩ Gp) :=
    GlobalTheory.T.weil_whittaker_central_twist F E χ σ μ lam c Φ hΦ _
      (GlobalTheory.T.weil_whittaker_support_bound_quadratic F E χ σ μ lam c Φ hχ hal hc hΦ.1)
  have m1 := measurable_indicator_of_continuousOn c1 (hA1.measurableSet.inter hGo.measurableSet)
  have m0 := measurable_indicator_of_continuousOn c0 (hA0.measurableSet.inter hGo.measurableSet)
  have e : GL2LocalData.Wc χ σ μ lam c Φ =
      ({g : GL (Fin 2) F | g.val 1 0 ≠ 0} ∩ Gp).indicator (GL2LocalData.Wc χ σ μ lam c Φ) +
      ({g : GL (Fin 2) F | g.val 1 0 = 0} ∩ Gp).indicator (GL2LocalData.Wc χ σ μ lam c Φ) := by
    ext g
    by_cases hg : g ∈ Gp
    · by_cases h0 : g.val 1 0 = 0
      · simp [Set.indicator, hg, h0]
      · simp [Set.indicator, hg, h0]
    · have : GL2LocalData.Wc χ σ μ lam c Φ g = 0 := Wc_eq_zero χ σ μ lam c Φ g hg
      simp [Set.indicator, hg, this]
  rw [e]
  exact m1.add m0

end Meas

theorem temperedBoundGL2_compact_whittaker : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → ∀ σ : E ≃ₐ[F] E, σ ≠ AlgEquiv.refl → ∀ (lam : ℂ) (c : Eˣ →* ℂˣ), IsUnit1 c → ∀ Φ ∈ GL2LocalData.SBc F E c, ∀ h₀ : GL (Fin 2) F, TemperedBoundGL2 (fun g => GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) lam c Φ (g * h₀)) := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ h2 hal σ hσ lam c hc Φ hΦ h₀
  haveI : ValuativeExtension F E := GlobalTheory.LBC.Inh.valuativeExtension hal
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsSeparable F E := inferInstance
  haveI : Fact (Module.finrank F E = 2) := ⟨h2⟩
  set μ := selfDualMeasure (GL2LocalData.chE E χ) with hμ
  have hmeas := measurable_Wc χ hχ hal σ hσ μ lam c hc Φ hΦ
  refine ⟨hmeas.comp (continuous_mul_right h₀).measurable, fun ε h0 h1 => ?_⟩
  obtain ⟨C0, B0, hC0, hB0, H0⟩ := GlobalTheory.T.weil_whittaker_diag_norm_le_sqrt_modulus_and_support F E χ σ μ lam c Φ hc hΦ.1 hΦ.2.1 h₀
  obtain ⟨C1, B1, hC1, hB1, H1⟩ := GlobalTheory.T.weil_whittaker_nontrivial_character_extension F E χ hχ hχ1 σ hσ μ lam c hc Φ hΦ.1 hΦ.2.1 h₀
  have hB : 0 < max B0 B1 := lt_max_of_lt_left hB0
  have hC : 0 ≤ max C0 C1 := le_max_of_le_left hC0
  refine ⟨max C0 C1 * (max B0 B1) ^ ε, max B0 B1, fun x y k hk => ?_⟩
  show ‖GL2LocalData.Wc χ σ μ lam c Φ (dg2 x y * k * h₀)‖ ≤ _ ∧ (GL2LocalData.Wc χ σ μ lam c Φ (dg2 x y * k * h₀) ≠ 0 → _)
  have hr : 0 < (modulus ((x / y : Fˣ) : F) : ℝ) := by
    exact_mod_cast modulus_pos (Units.ne_zero _)
  have key : ‖GL2LocalData.Wc χ σ μ lam c Φ (dg2 x y * k * h₀)‖ ≤
        max C0 C1 * (modulus ((x / y : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ) ∧
      (GL2LocalData.Wc χ σ μ lam c Φ (dg2 x y * k * h₀) ≠ 0 → (modulus ((x / y : Fˣ) : F) : ℝ) ≤ max B0 B1) := by
    by_cases hz : (k * h₀).val 1 0 = 0
    · obtain ⟨a, b⟩ := H0 x y k hk hz
      exact ⟨a.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hr.le _)),
        fun h => (b h).trans (le_max_left _ _)⟩
    · obtain ⟨a, b⟩ := H1 x y k hk hz
      exact ⟨a.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hr.le _)),
        fun h => (b h).trans (le_max_right _ _)⟩
  refine ⟨?_, key.2⟩
  by_cases hW : GL2LocalData.Wc χ σ μ lam c Φ (dg2 x y * k * h₀) = 0
  · rw [hW, norm_zero]
    exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hB.le _)) (Real.rpow_nonneg hr.le _)
  · have hle := key.2 hW
    have e : (modulus ((x / y : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ) =
        (modulus ((x / y : Fˣ) : F) : ℝ) ^ ε * (modulus ((x / y : Fˣ) : F) : ℝ) ^ (1 / 2 - ε) := by
      rw [← Real.rpow_add hr]
      congr 1
      ring
    have hpow : (modulus ((x / y : Fˣ) : F) : ℝ) ^ ε ≤ (max B0 B1) ^ ε :=
      Real.rpow_le_rpow hr.le hle h0.le
    calc ‖GL2LocalData.Wc χ σ μ lam c Φ (dg2 x y * k * h₀)‖
        ≤ max C0 C1 * (modulus ((x / y : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ) := key.1
      _ = max C0 C1 * ((modulus ((x / y : Fˣ) : F) : ℝ) ^ ε * (modulus ((x / y : Fˣ) : F) : ℝ) ^ (1 / 2 - ε)) := by
          rw [e]
      _ ≤ max C0 C1 * ((max B0 B1) ^ ε * (modulus ((x / y : Fˣ) : F) : ℝ) ^ (1 / 2 - ε)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hr.le _)) hC
      _ = max C0 C1 * (max B0 B1) ^ ε * (modulus ((x / y : Fˣ) : F) : ℝ) ^ (1 / 2 - ε) := by ring

end GlobalTheory.CompanionTheory.WcB
