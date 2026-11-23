import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilChoice

section Lin

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem rW_const_mul (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (a b c d : F)
    (k : ℂ) (Φ : E → ℂ) (z : E) :
    rW χ σ μE lam a b c d (fun y => k * Φ y) z = k * rW χ σ μE lam a b c d Φ z := by
  rw [rW, rW]
  split_ifs with hc
  · ring
  · have e : ∫ u, (χ ((a * Algebra.norm F z + d * Algebra.norm F u -
          Algebra.trace F E (σ z * u)) / c) : ℂ) * (k * Φ u) ∂μE =
        k * ∫ u, (χ ((a * Algebra.norm F z + d * Algebra.norm F u -
          Algebra.trace F E (σ z * u)) / c) : ℂ) * Φ u ∂μE := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      show (χ _ : ℂ) * (k * Φ u) = k * ((χ _ : ℂ) * Φ u)
      ring
    rw [e]
    ring

end Lin

theorem wchoice : Ad3.K.GL2LocalData.WChoice := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη c Φ hΦ g t ht
  have h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det := ⟨t, ht⟩
  have h0 : Algebra.norm F (h.choose : E) = (g.val).det := h.choose_spec
  have hne : Algebra.norm F (h.choose : E) ≠ 0 :=
    (h.choose.isUnit.map (Algebra.norm F : E →* F)).ne_zero
  obtain ⟨u, hu⟩ : ∃ u : Eˣ, t = h.choose * u := ⟨h.choose⁻¹ * t, by group⟩
  have hN : Algebra.norm F (u : E) = 1 := by
    have e : Algebra.norm F (h.choose : E) * Algebra.norm F (u : E) =
        Algebra.norm F (h.choose : E) * 1 := by
      rw [← map_mul, ← Units.val_mul, ← hu, ht, h0, mul_one]
    exact mul_left_cancel₀ hne e
  have hfun : (fun y => Φ (y * (t : E))) =
      fun y => (((c u)⁻¹ : ℂˣ) : ℂ) * Φ (y * (h.choose : E)) := by
    funext y
    rw [hu, Units.val_mul, ← mul_assoc]
    exact hΦ.2.2 u hN _
  have hcu : ((c u : ℂˣ) : ℂ) * (((c u)⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  show Wc χ σ (muE E χ) (lamE E χ η) c Φ g = _
  rw [Wc, dif_pos h, hfun, rW_const_mul, hu, map_mul, Units.val_mul]
  linear_combination (-(((c h.choose : ℂˣ) : ℂ) * (((modulus (g.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) *
      rW χ σ (muE E χ) (lamE E χ η) (g.val 0 0 / (g.val).det) (g.val 0 1)
        (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => Φ (x * (h.choose : E))) 1)) * hcu

end GlobalTheory.CompanionTheory.WeilChoice
