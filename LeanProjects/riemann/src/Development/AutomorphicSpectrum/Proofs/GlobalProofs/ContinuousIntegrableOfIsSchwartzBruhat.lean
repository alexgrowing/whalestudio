import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralSelfDualEqAdelicFourier
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiInt

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.FouCoord GroundTheory.Automorphic.GJMatrix
open scoped NNReal

theorem continuous_integrable_of_isSchwartzBruhat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (dx : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), dx.IsAddHaarMeasure → ∀ Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ, IsSchwartzBruhat Φ → Continuous Φ ∧ Integrable Φ dx := by
  intro F E _ _ _ _ _ σ hCM M dx hdx Φ hΦ
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  obtain ⟨h1, -, -, -, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := h1
  haveI := hBor 1 M
  have hf := (isSchwartzBruhat_iff b Φ).1 hΦ
  let e := crd (AF F) b M
  have hcomp : (Φ ∘ e.symm) ∘ e = Φ := by
    funext X
    simp
  have hcont : Continuous Φ := by
    have h : Continuous ((Φ ∘ e.symm) ∘ e) :=
      (continuous_of_mem_schwartzBruhatPi hf).comp e.continuous
    rwa [hcomp] at h
  refine ⟨hcont, ?_⟩
  haveI : LocallyCompactSpace (Fin 1 → Fin M → AF F ⊗[F] E) :=
    e.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Fin 1 → Fin M → AF F ⊗[F] E) :=
    e.toHomeomorph.secondCountableTopology
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, dx = c • mu0 e := ⟨_, Measure.isAddLeftInvariant_eq_smul dx (mu0 e)⟩
  have hI : Integrable Φ (mu0 e) := by
    rw [mu0, (measurableEmbedding_symm e).integrable_map_iff]
    exact integrable_of_mem_schwartzBruhatPi hf
  rw [hc]
  exact hI.smul_measure_nnreal

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiInt
