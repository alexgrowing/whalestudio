import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne
import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TraceGramDetNeZero
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsEqAdelicCharMul
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHomeomorphRankOneTuples
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteComponentCoordinatesAction
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateBijectionTraceForm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TupOfCv
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSchwartzBruhatCompactSupportNonzeroStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth

section Gen
open NumberField IsDedekindDomain MeasureTheory
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Heights₂.Theta
open scoped TensorProduct ENNReal Matrix NumberField.AdeleRing

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_test : ∃ f ∈ schwartzBruhatPi F ι, HasCompactSupport f ∧ f 0 ≠ 0 := GlobalTheory.T.exists_schwartzBruhat_compact_support_nonzero F ι

theorem selfDual_eq (G : Matrix ι ι F) (hs : G.IsSymm) (hG : G.det ≠ 0) (ν : Measure (ι → 𝔸[F]))
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual ν (chiG G)) : ν = adeleMeasurePi F := by
  obtain ⟨f0, hf0, hcs, h0⟩ := exists_test (F := F) (ι := ι)
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  have hNM : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hu
  have hMN : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hu
  set Gm := G.map (algebraMap F 𝔸[F]) with hGm
  have hH := h.1
  have e : ν = Measure.addHaarScalarFactor ν (adeleMeasurePi F) • adeleMeasurePi F :=
    Measure.isAddLeftInvariant_eq_smul ν (adeleMeasurePi F)
  set c : NNReal := Measure.addHaarScalarFactor ν (adeleMeasurePi F) with hcdef

  have hT0 : ∀ (g : (ι → 𝔸[F]) → ℂ) y, ∫ x, g x * chiG G x y ∂(adeleMeasurePi F) = adelicFourierPi F g (Gm *ᵥ y) := fun g y => rfl
  have hT : ∀ (g : (ι → 𝔸[F]) → ℂ) y, ∫ x, g x * chiG G x y ∂ν = (c : ℂ) * adelicFourierPi F g (Gm *ᵥ y) := by
    intro g y
    rw [e, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, hT0]
  set g1 : (ι → 𝔸[F]) → ℂ := fun y => adelicFourierPi F f0 (Gm *ᵥ y) with hg1
  have hg1m : g1 ∈ schwartzBruhatPi F ι :=
    comp_mulVec_mem_schwartzBruhatPi G G⁻¹ hNM hMN (adelicFourierPi_mem_schwartzBruhatPi hf0)
  have hI : Integrable (fun y => ∫ x, f0 x * chiG G x y ∂ν) ν := by
    simp only [hT]
    rw [e]
    exact ((integrable_of_mem_schwartzBruhatPi hg1m).const_mul (c : ℂ)).smul_measure_nnreal
  have h2 := h.2 f0 (continuous_of_mem_schwartzBruhatPi hf0) hcs hI 0
  simp only [hT] at h2
  have h3 : adelicFourierPi F (fun x => (c : ℂ) * adelicFourierPi F f0 (Gm *ᵥ x)) (Gm *ᵥ 0) =
      (c : ℂ) * adelicFourierPi F g1 (Gm *ᵥ 0) :=
    congrFun (adelicFourierPi_smul (c : ℂ) g1) _
  have h4 : adelicFourierPi F g1 (Gm *ᵥ 0) = f0 0 := by
    rw [Matrix.mulVec_zero, hg1, adelicFourierPi_comp_mulVec G G⁻¹ hNM hMN, Matrix.mulVec_zero,
      adelicFourierPi_adelicFourierPi hf0]
    simp
  rw [h3, h4, neg_zero, ← mul_assoc] at h2
  have h5 : ((c : ℂ)) * (c : ℂ) = 1 := mul_right_cancel₀ h0 (by rw [h2, one_mul])
  have h6 : c * c = 1 := by exact_mod_cast h5
  have h7 : c = 1 := by
    have : (c : ℝ) * c = 1 := by exact_mod_cast h6
    have h8 : (c : ℝ) = 1 := by nlinarith [c.coe_nonneg]
    exact_mod_cast h8
  rw [e, h7, one_smul]

theorem selfDual_transport {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [TopologicalSpace V'] [IsTopologicalAddGroup V']
    [MeasurableSpace V'] [BorelSpace V'] (e : V ≃ₜ V') (he : ∀ x y, e (x + y) = e x + e y)
    (χ : V → V → ℂ) (χ' : V' → V' → ℂ) (hχ : ∀ x y, χ' (e x) (e y) = χ x y) (μ : Measure V)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual μ χ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual (μ.map e) χ' := by
  have hμ := h.1
  let a : V ≃+ V' := AddEquiv.mk' e.toEquiv he
  have ha : ∀ x, a x = e x := fun _ => rfl
  refine ⟨a.isAddHaarMeasure_map μ e.continuous e.symm.continuous, fun Φ hc hs hI z => ?_⟩
  have hemb := e.measurableEmbedding
  set Φ0 : V → ℂ := fun x => Φ (e x) with hΦ0
  have hT : ∀ y, ∫ x, Φ x * χ' x (e y) ∂(μ.map e) = ∫ x, Φ0 x * χ x y ∂μ := by
    intro y
    rw [hemb.integral_map]
    simp only [hΦ0, hχ]
  have hI' : Integrable (fun y => ∫ x, Φ0 x * χ x y ∂μ) μ := by
    have h1 := (hemb.integrable_map_iff).1 hI
    exact h1.congr (Filter.Eventually.of_forall fun y => by simp only [Function.comp_apply, hT])
  have h2 := h.2 Φ0 (hc.comp e.continuous) (hs.comp_homeomorph e) hI' (e.symm z)
  rw [hemb.integral_map]
  have h3 : Φ0 (-e.symm z) = Φ (-z) := by
    simp only [hΦ0]
    rw [← ha, map_neg, ha, e.apply_symm_apply]
  rw [← h3, ← h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only []
  rw [hT y, ← hχ y (e.symm z), e.apply_symm_apply]

end Gen

section Link
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Heights₂.Theta
open GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.CoordMat
open scoped TensorProduct ENNReal Matrix NumberField.AdeleRing
attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end Link

section Main
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

end Main
end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth
