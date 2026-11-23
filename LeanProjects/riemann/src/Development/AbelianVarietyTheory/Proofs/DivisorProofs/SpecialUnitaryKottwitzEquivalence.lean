import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
open NumberField
open scoped TensorProduct Matrix

namespace GlobalTheory.SEquivOfRat

open Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol IsDedekindDomain

theorem ratM_det {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (γ : Matrix (Fin r) (Fin r) E) :
    (ratM (maximalRealSubfield E) γ).det = (1 : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ γ.det := by
  have h : ratM (maximalRealSubfield E) γ = (Algebra.TensorProduct.includeRight :
      E →ₐ[maximalRealSubfield E] RA (maximalRealSubfield E) E).toRingHom.mapMatrix γ := rfl
  rw [h, ← RingHom.map_det]; rfl

theorem sequiv_of_rat {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (G : Matrix (Fin r) (Fin r) E)
    (L : Set (Fin r → E)) (s s' M : Matrix (Fin r) (Fin r) (GlobalTheory.AdLat.RA (maximalRealSubfield E) E))
    (γ : Matrix (Fin r) (Fin r) E) (hs : GlobalTheory.SUVol.IsSA G s) (hs' : GlobalTheory.SUVol.IsSA G s')
    (hM : GlobalTheory.UCls.IsKM (IsCMField.complexConj E) G L 1 M)
    (h : s' * M = GlobalTheory.UCls.ratM (maximalRealSubfield E) γ * s) (hγ : γ.det = 1) :
    GlobalTheory.SUVol.SEquiv G L 1 s' s := by
  have hγu : IsUnit γ.det := by rw [hγ]; exact isUnit_one
  have hinv : γ * γ⁻¹ = 1 := Matrix.mul_nonsing_inv γ hγu
  have hinv' : γ⁻¹ * γ = 1 := Matrix.nonsing_inv_mul γ hγu
  have hdγ : (ratM (maximalRealSubfield E) γ).det = 1 := by rw [ratM_det, hγ]; rfl
  have hdγi : (ratM (maximalRealSubfield E) γ⁻¹).det = 1 := by
    have := congrArg Matrix.det (ratM_mul (E := E) γ γ⁻¹)
    rw [hinv, ratM_one, det_one, det_mul, hdγ, one_mul] at this
    exact this.symm
  have hsu : IsUnit s.det := by rw [hs.2]; exact isUnit_one
  have hss : s * s⁻¹ = 1 := Matrix.mul_nonsing_inv s hsu

  have hpres : ∀ x y, hermA (IsCMField.complexConj E) G (ratM (maximalRealSubfield E) γ *ᵥ x) (ratM (maximalRealSubfield E) γ *ᵥ y) =
      hermA (IsCMField.complexConj E) G x y := by
    intro x y
    have ex : ∀ z, ratM (maximalRealSubfield E) γ *ᵥ z = s' *ᵥ (M *ᵥ (s⁻¹ *ᵥ z)) := by
      intro z
      rw [mulVec_mulVec, mulVec_mulVec, h, Matrix.mul_assoc, hss, Matrix.mul_one]
    rw [ex, ex, hs'.1.2, hM.1.2, ← hs.1.2]
    simp only [mulVec_mulVec, hss, one_mulVec]
  refine ⟨γ⁻¹, ⟨⟨by rw [hdγi]; exact isUnit_one, fun x y => ?_⟩, hdγi⟩, M, hM, ?_, ?_⟩
  · rw [← hpres, mulVec_mulVec, mulVec_mulVec, ← ratM_mul, hinv, ratM_one, one_mulVec, one_mulVec]
  · have := congrArg Matrix.det h
    rw [det_mul, det_mul, hs'.2, hs.2, hdγ, one_mul, mul_one] at this
    exact this
  · rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, ← ratM_mul, hinv', ratM_one, Matrix.one_mul]

end GlobalTheory.SEquivOfRat
