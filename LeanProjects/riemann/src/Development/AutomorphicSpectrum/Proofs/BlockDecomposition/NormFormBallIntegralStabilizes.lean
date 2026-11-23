import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnstatedLocalWeilLemma

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSB

theorem ballIntegral_stable :
    (ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (a : Fˣ), ∀ Φ ∈ SBE E, ∃ n₀ : ℤ, ∀ n ≤ n₀,
      ∫ u, (χ ((a : F) * Algebra.norm F u) : ℂ) * FTE E χ σ Φ u ∂muE E χ =
        (∫ u in (valBall E n : Set E), (χ ((a : F) * Algebra.norm F u) : ℂ) ∂muE E χ) *
          ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂muE E χ) →
    ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (a : Fˣ), ∃ (c : ℂ) (n₀ : ℤ), ∀ n ≤ n₀,
      ∫ u in (valBall E n : Set E), (χ ((a : F) * Algebra.norm F u) : ℂ) ∂muE E χ = c := by
  intro H F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη a
  haveI : Fact (Module.finrank F E = 2) := ⟨hfr⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : ValuativeExtension F E := valuativeExtension_of_continuous hcont
  haveI : Algebra.IsSeparable F E := inferInstance
  have hN := continuous_norm_of (F := F) (E := E) hcont
  have hlc := isLocallyConstant_char hχ hχ1
  have hf : IsLocallyConstant (fun z : E => (χ (-(Algebra.norm F z) / a) : ℂ)) :=
    hlc.comp_continuous (hN.neg.div_const _)
  have h0 : (χ (-(Algebra.norm F (0 : E)) / a) : ℂ) = 1 := by
    simp [Algebra.norm_zero]
  have hU : {z : E | (χ (-(Algebra.norm F z) / a) : ℂ) = 1} ∈ nhds (0 : E) :=
    (hf.isOpen_fiber 1).mem_nhds h0
  obtain ⟨m, -, hm⟩ := hasBasis_nhds_zero_valBall.mem_iff.1 hU
  have hclopen : IsClopen (valBall E m : Set E) := ⟨isClosed_valBall m, isOpen_valBall m⟩
  have hΦ₀ : (valBall E m : Set E).indicator (fun _ => (1 : ℂ)) ∈ SBE E :=
    ⟨by
        have h : IsLocallyConstant (⇑(LocallyConstant.charFn ℂ hclopen)) :=
          LocallyConstant.isLocallyConstant _
        rw [LocallyConstant.coe_charFn] at h
        exact h,
      HasCompactSupport.intro (isCompact_valBall m) fun x hx => Set.indicator_of_notMem hx _⟩
  obtain ⟨n₀, hn₀⟩ := H F χ hχ hχ1 E hfr hcont σ hσ η hη a _ hΦ₀
  have hJ : ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) *
      (valBall E m : Set E).indicator (fun _ => (1 : ℂ)) z ∂muE E χ =
      (((muE E χ).real (valBall E m : Set E) : ℝ) : ℂ) := by
    have e : (fun z => (χ (-(Algebra.norm F z) / a) : ℂ) *
        (valBall E m : Set E).indicator (fun _ => (1 : ℂ)) z) =
        (valBall E m : Set E).indicator (fun _ => (1 : ℂ)) := by
      funext z
      by_cases hz : z ∈ (valBall E m : Set E)
      · rw [Set.indicator_of_mem hz, mul_one]
        exact hm hz
      · rw [Set.indicator_of_notMem hz, mul_zero]
    rw [e, integral_indicator hclopen.isOpen.measurableSet]
    simp
  have hV : (muE E χ).real (valBall E m : Set E) ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨(hclopen.isOpen.measure_pos _ ⟨0, zero_mem _⟩).ne',
      (isCompact_valBall m).measure_lt_top.ne⟩
  have hV' : (((muE E χ).real (valBall E m : Set E) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hV
  refine ⟨(∫ u, (χ ((a : F) * Algebra.norm F u) : ℂ) *
      FTE E χ σ ((valBall E m : Set E).indicator (fun _ => (1 : ℂ))) u ∂muE E χ) /
      (((muE E χ).real (valBall E m : Set E) : ℝ) : ℂ), n₀, fun n hn => ?_⟩
  rw [hn₀ n hn, hJ, mul_div_cancel_right₀ _ hV']

end GlobalTheory.CompanionTheory.WeilSB
