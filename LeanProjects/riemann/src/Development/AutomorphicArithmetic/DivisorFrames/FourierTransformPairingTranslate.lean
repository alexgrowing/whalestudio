import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB
import Development.AutomorphicArithmetic.DivisorFrames.FourierSchwartzBruhatPreserved
import Development.AutomorphicArithmetic.DivisorFrames.HaarIntegralUnitsScaling
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeBumpB
open scoped GlobalTheory.VacAny

private theorem UpperTheory.fourier_pairing_translate_of_substitution {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] (m : Measure A) [m.IsAddHaarMeasure] (χ : A → ℂ) (hχ : Continuous χ)
    (y : Aˣ) (c : ℂ) (hsub : ∀ f : A → ℂ, ∫ s, f s ∂m = c * ∫ s, f ((y : A) * s) ∂m)
    (T₁ T₂ : A → ℂ) (h₁ : Continuous T₁) (h₁c : HasCompactSupport T₁) (h₂ : Continuous T₂)
    (h₂c : HasCompactSupport T₂) :
    ∫ x, (∫ s, T₂ s * χ (x * s) ∂m) * T₁ (x * (y : A)) ∂m = ∫ x, (∫ s, T₁ s * χ (x * s) ∂m) * T₂ (x * (y : A)) ∂m := by
  have key : ∀ S T : A → ℂ, ∫ x, (∫ s, S s * χ (x * s) ∂m) * T (x * (y : A)) ∂m =
      c * ∫ x, ∫ s, T ((y : A) * x) * S ((y : A) * s) * χ (x * (y : A) * s) ∂m ∂m := by
    intro S T
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [hsub fun s => S s * χ (x * s), mul_assoc, ← integral_mul_const]
    congr 2
    funext s
    rw [mul_comm x (y : A), mul_left_comm x, ← mul_assoc (y : A)]
    ring
  have hcs : ∀ T : A → ℂ, HasCompactSupport T → HasCompactSupport fun x => T ((y : A) * x) := fun T hT =>
    hT.comp_homeomorph (Homeomorph.smul y)
  rw [key, key]
  congr 1
  rw [integral_integral_swap]
  · congr 1
    funext x
    congr 1
    funext s
    rw [show s * (y : A) * x = x * (y : A) * s by ring]
    ring
  · refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · change Continuous fun z : A × A => T₁ ((y : A) * z.1) * T₂ ((y : A) * z.2) * χ (z.1 * (y : A) * z.2)
      fun_prop
    · refine HasCompactSupport.intro ((hcs T₁ h₁c).isCompact.prod (hcs T₂ h₂c).isCompact) fun z hz => ?_
      change T₁ ((y : A) * z.1) * T₂ ((y : A) * z.2) * χ (z.1 * (y : A) * z.2) = 0
      rcases not_and_or.1 hz with h | h
      · rw [image_eq_zero_of_notMem_tsupport h, zero_mul, zero_mul]
      · rw [image_eq_zero_of_notMem_tsupport h, mul_zero, zero_mul]

theorem UpperTheory.fourier_transform_pairing_translate :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
        ∀ [MeasurableSpace (Fv F v ⊗[F] E)] [BorelSpace (Fv F v ⊗[F] E)] (m : Measure (Fv F v ⊗[F] E)) [m.IsAddHaarMeasure], ∀ T₁ ∈ SB (Fv F v ⊗[F] E), ∀ T₂ ∈ SB (Fv F v ⊗[F] E), ∀ y : (Fv F v ⊗[F] E)ˣ,
          ∫ x, four v ψ m T₂ x * T₁ (x * (y : Fv F v ⊗[F] E)) ∂m = ∫ x, four v ψ m T₁ x * T₂ (x * (y : Fv F v ⊗[F] E)) ∂m := by
  intro F E _ _ _ _ _ v ψ hc _ _ _ m _ T₁ hT₁ T₂ hT₂ y
  haveI := GlobalTheory.LocTateInt.isTopologicalRing_Ev (E := E) v
  haveI := GlobalTheory.LocTateInt.t2Space_Fv_tensor (E := E) v
  haveI := GlobalTheory.LocTateInt.isModuleTopology_Ev (E := E) v
  haveI := GlobalTheory.LocTateInt.locallyCompactSpace_Ev (E := E) v
  haveI := GlobalTheory.LocTateInt.secondCountable_Ev (E := E) v
  obtain ⟨h₁, h₁c⟩ := hT₁
  obtain ⟨h₂, h₂c⟩ := hT₂
  refine UpperTheory.fourier_pairing_translate_of_substitution m (fun a => ψ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) a))
    (hc.comp (IsModuleTopology.continuous_of_linearMap (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)))) y
    (((GlobalTheory.Doubling.absEv F E v ((y⁻¹ : (Fv F v ⊗[F] E)ˣ)) : ℝ) : ℂ))⁻¹ (fun f => ?_) T₁ T₂
    (IsLocallyConstant.continuous h₁) h₁c (IsLocallyConstant.continuous h₂) h₂c
  have h := UpperTheory.haar_integral_units_scaling F E v m y⁻¹ fun s => f ((y : Fv F v ⊗[F] E) * s)
  simpa only [Units.mul_inv_cancel_left] using h
