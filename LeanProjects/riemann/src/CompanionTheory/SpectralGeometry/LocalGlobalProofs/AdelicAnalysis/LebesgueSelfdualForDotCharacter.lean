import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RealFourier

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem fourierChar_smul (t : ℝ) (c : ℂ) :
    (Real.fourierChar t : Circle) • c = c * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := by
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

theorem inversion_neg (ι : Type) [Fintype ι] (Φ : (ι → ℝ) → ℂ) (hc : Continuous Φ)
    (hs : HasCompactSupport Φ)
    (hi : Integrable (fun y : ι → ℝ => ∫ x : ι → ℝ,
      Φ x * Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ))) volume)
    (z : ι → ℝ) :
    ∫ y : ι → ℝ, (∫ x : ι → ℝ,
        Φ x * Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ))) *
      Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (y ⬝ᵥ z) : ℝ) : ℝ)) = Φ (-z) := by
  have mp := PiLp.volume_preserving_toLp ι
  have emb : MeasurableEmbedding (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) :=
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding
  have hin : ∀ x y : ι → ℝ, inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ ι) (WithLp.toLp 2 y)
      = x ⬝ᵥ y := by
    intro x y
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct_comm]
  set Ψ : EuclideanSpace ℝ ι → ℂ := fun u => Φ u.ofLp with hΨ
  have hΨc : Continuous Ψ := hc.comp (PiLp.continuous_ofLp 2 _)
  have hΨi : Integrable Ψ volume :=
    (mp.integrable_comp_emb emb).1 (hc.integrable_of_hasCompactSupport hs)
  have hF : ∀ y : ι → ℝ, FourierTransform.fourier Ψ (WithLp.toLp 2 y) = ∫ x : ι → ℝ,
      Φ x * Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ)) := by
    intro y
    rw [Real.fourier_eq, ← mp.integral_comp emb]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hin, fourierChar_smul, hΨ]
    simp
  have hFi : Integrable (FourierTransform.fourier Ψ) volume := by
    refine (mp.integrable_comp_emb emb).1 ?_
    refine hi.congr (Filter.Eventually.of_forall fun y => ?_)
    exact (hF y).symm
  have hinv := congrFun (hΨc.fourierInv_fourier_eq hΨi hFi) (WithLp.toLp 2 (-z))
  rw [Real.fourierInv_eq, ← mp.integral_comp emb] at hinv
  have hval : Ψ (WithLp.toLp 2 (-z)) = Φ (-z) := rfl
  rw [← hval, ← hinv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [hin, fourierChar_smul, hF]
  simp

end GlobalTheory.CompanionTheory.SW.RealFourier

namespace GlobalTheory.CompanionTheory.SW

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem selfDual_real_coord : ∀ (ι : Type) [Fintype ι] (ε : ℝ), ε = 1 ∨ ε = -1 →
    SelfDual (volume : Measure (ι → ℝ))
      (fun x y => Complex.exp (2 * Real.pi * Complex.I * (ε * (x ⬝ᵥ y) : ℝ))) := by
  intro ι _ ε hε
  refine ⟨inferInstance, fun Φ hc hs hi z => ?_⟩
  rcases hε with rfl | rfl
  ·
    have hG : ∀ y : ι → ℝ, (∫ x : ι → ℝ,
        Φ x * Complex.exp (2 * Real.pi * Complex.I * (((1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ))) =
        ∫ x : ι → ℝ, (fun u => Φ (-u)) x *
          Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ)) := by
      intro y
      rw [← integral_neg_eq_self (fun x : ι → ℝ =>
        Φ x * Complex.exp (2 * Real.pi * Complex.I * (((1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ))) volume]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp
    have hc' : Continuous fun u : ι → ℝ => Φ (-u) := hc.comp continuous_neg
    have hs' : HasCompactSupport fun u : ι → ℝ => Φ (-u) :=
      hs.comp_homeomorph (Homeomorph.neg (ι → ℝ))
    have hi' : Integrable (fun y : ι → ℝ => ∫ x : ι → ℝ, (fun u => Φ (-u)) x *
        Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ))) volume :=
      hi.congr (Filter.Eventually.of_forall hG)
    have key := RealFourier.inversion_neg ι (fun u => Φ (-u)) hc' hs' hi' (-z)
    simp only [neg_neg] at key
    rw [← key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hG y]
    simp
  · exact RealFourier.inversion_neg ι Φ hc hs hi z

end GlobalTheory.CompanionTheory.SW
