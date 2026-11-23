import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.SfiniteMuN

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.Cv

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

theorem sigAll : SigAll := by
  intro k r ε lam H _ _ σ hσ
  obtain ⟨P, ⟨⟨-, hPJ⟩, hPu⟩, hDS⟩ := hσ
  obtain ⟨-, -, ⟨⟨h1, hmul⟩, hnorm, -⟩, -⟩ := hDS
  have hQ1 : Pᴴ * P = 1 := by
    first
    | exact Unitary.star_mul_self_of_mem hPu
    | exact Matrix.mem_unitaryGroup_iff'.mp hPu
    | exact hPu.1
  have hQ2 : P * Pᴴ = 1 := by
    first
    | exact Unitary.mul_star_self_of_mem hPu
    | exact Matrix.mem_unitaryGroup_iff.mp hPu
    | exact hPu.2
  have hinv : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv hQ1
  have hQ1' : ∀ x : Mx k r, Pᴴ * (P * x) = x := fun x => by rw [← mul_assoc, hQ1, one_mul]
  have hQ2' : ∀ x : Mx k r, P * (Pᴴ * x) = x := fun x => by rw [← mul_assoc, hQ2, one_mul]
  have hc : ∀ h : Mx k r, P⁻¹ * (P * h * Pᴴ) * P = h := fun h => by
    simp only [hinv, mul_assoc, hQ1', hQ1, mul_one]
  have hc2 : ∀ a b : Mx k r, P⁻¹ * (P * a * Pᴴ * (P * b * Pᴴ)) * P = a * b := fun a b => by
    simp only [hinv, mul_assoc, hQ1', hQ1, mul_one]
  have hmem : ∀ a ∈ UH (Hpk k r), P * a * Pᴴ ∈ UJset ε := by
    intro a ha
    have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
    show (P * a * Pᴴ)ᴴ * Formalism.REAL.Jm ε * (P * a * Pᴴ) = Formalism.REAL.Jm ε
    calc (P * a * Pᴴ)ᴴ * Formalism.REAL.Jm ε * (P * a * Pᴴ)
        = P * (aᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * a) * Pᴴ := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc]
      _ = P * (Pᴴ * Formalism.REAL.Jm ε * P) * Pᴴ := by rw [hPJ, ha']
      _ = Formalism.REAL.Jm ε := by simp only [mul_assoc, hQ2, mul_one, hQ2']
  have h1' : σ (P⁻¹ * 1 * P) = 1 := h1
  have hmul' : ∀ x ∈ UJset ε, ∀ y ∈ UJset ε,
      σ (P⁻¹ * (x * y) * P) = (σ (P⁻¹ * x * P)).comp (σ (P⁻¹ * y * P)) := hmul
  have hnorm' : ∀ g ∈ UJset ε, ∀ v : H, ‖σ (P⁻¹ * g * P) v‖ = ‖v‖ := hnorm
  refine ⟨?_, fun a ha b hb => ?_, fun a ha x => ?_⟩
  · rwa [mul_one, hinv, hQ1] at h1'
  · have e := hmul' _ (hmem a ha) _ (hmem b hb)
    rwa [hc2, hc, hc] at e
  · have e := hnorm' _ (hmem a ha) x
    rwa [hc] at e

end PI.WBL.Cv
