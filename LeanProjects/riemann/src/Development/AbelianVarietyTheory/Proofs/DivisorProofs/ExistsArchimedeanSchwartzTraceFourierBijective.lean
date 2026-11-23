import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FourierInversionHaarSymmForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.ArchFourier

open scoped FourierTransform SchwartzMap

theorem exists_schwartz_fourier_form {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : ∀ x y, B x y = B y x)
    (hn : ∀ x, (∀ y, B x y = 0) → x = 0) (μ : Measure V) [μ.IsAddHaarMeasure] :
    ∃ ei : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ), Function.Bijective ei ∧ ∀ (f : 𝓢(V, ℂ)) (y : V),
      ei f y = ∫ x, f x * Complex.exp (-(2 * Real.pi * Complex.I) * (B x y : ℂ)) ∂μ := by
  let T := toEuclidean (E := V)
  obtain ⟨R, hR⟩ := GlobalTheory.exists_equiv_inner_eq_form T B hs hn
  obtain ⟨a, ha, haI, -⟩ := GlobalTheory.exists_pos_integral_comp_equiv_haar T μ
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  let CR := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) R
  let CT := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) T.symm
  let CRi := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) R.symm
  let CTi := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) T
  let Fo := SchwartzMap.fourierTransformCLM ℂ (V := EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) (E := ℂ)
  have h1 : ∀ g, CRi (CR g) = g := fun g => by ext x; simp [CRi, CR]
  have h2 : ∀ g, CR (CRi g) = g := fun g => by ext x; simp [CRi, CR]
  have h3 : ∀ g, CTi (CT g) = g := fun g => by ext x; simp [CTi, CT]
  have h4 : ∀ g, CT (CTi g) = g := fun g => by ext x; simp [CTi, CT]
  have h5 : ∀ g, 𝓕⁻ (Fo g) = g := fun g => by
    simp only [Fo, SchwartzMap.fourierTransformCLM_apply]; exact FourierTransform.fourierInv_fourier_eq g
  have h6 : ∀ g, Fo (𝓕⁻ g) = g := fun g => by
    simp only [Fo, SchwartzMap.fourierTransformCLM_apply]; exact FourierTransform.fourier_fourierInv_eq g
  refine ⟨(a : ℂ) • (CR.comp (Fo.comp CT)), ?_, fun f y => ?_⟩
  · rw [Function.bijective_iff_has_inverse]
    refine ⟨fun g => (a : ℂ)⁻¹ • CTi (𝓕⁻ (CRi g)), fun f => ?_, fun g => ?_⟩
    · simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul, h1, h5, h3,
        FourierTransform.fourierInv_smul, smul_smul, inv_mul_cancel₀ ha', one_smul]
    · change (a : ℂ) • CR (Fo (CT ((a : ℂ)⁻¹ • CTi (𝓕⁻ (CRi g))))) = g
      rw [map_smul, map_smul, map_smul, h4, h6, h2, smul_smul, mul_inv_cancel₀ ha', one_smul]
  · have e1 : ((a : ℂ) • (CR.comp (Fo.comp CT))) f y = (a : ℂ) * 𝓕 (fun w => f (T.symm w)) (R y) := rfl
    rw [e1, Real.fourier_eq', ← haI]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ContinuousLinearEquiv.symm_apply_apply, smul_eq_mul, hR]
    rw [mul_comm]
    congr 2
    push_cast
    ring

end GlobalTheory.ArchFourier

namespace GlobalTheory.ArchFourier

noncomputable def traceDot (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y))
    (fun x x' y => by simp only [add_dotProduct, map_add])
    (fun c x y => by simp only [smul_dotProduct, map_smul, smul_eq_mul])
    (fun x y y' => by simp only [dotProduct_add, map_add])
    (fun c x y => by simp only [dotProduct_smul, map_smul, smul_eq_mul])

theorem traceDot_apply {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x y : κ → mixedEmbedding.mixedSpace F) :
    traceDot F κ x y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y) := rfl

theorem traceDot_comm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x y : κ → mixedEmbedding.mixedSpace F) : traceDot F κ x y = traceDot F κ y x := by
  rw [traceDot_apply, traceDot_apply, dotProduct_comm]

theorem traceDot_nondeg {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x : κ → mixedEmbedding.mixedSpace F) (hx : ∀ y, traceDot F κ x y = 0) : x = 0 := by
  classical
  funext i
  refine GlobalTheory.ArchUniq.Coord.eq_zero_of_trace _ fun b => ?_
  have := hx (Pi.single i b)
  rwa [traceDot_apply, dotProduct_single] at this

theorem exists_fourier_sInf : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)]
    [BorelSpace (κ → mixedEmbedding.mixedSpace F)] (μ : Measure (κ → mixedEmbedding.mixedSpace F)) [μ.IsAddHaarMeasure],
    ∃ ei : SInf F κ →L[ℂ] SInf F κ, Function.Bijective ei ∧ ∀ (f : SInf F κ) (y : κ → mixedEmbedding.mixedSpace F),
      ei f y = ∫ x, f x * Complex.exp (-(2 * Real.pi * Complex.I) *
        (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y) : ℝ)) ∂μ := by
  intro F _ _ κ _ _ _ μ _
  classical
  exact exists_schwartz_fourier_form (traceDot F κ) traceDot_comm traceDot_nondeg μ

end GlobalTheory.ArchFourier
