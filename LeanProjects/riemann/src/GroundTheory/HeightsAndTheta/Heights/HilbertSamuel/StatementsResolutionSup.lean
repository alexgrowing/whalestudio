import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory

noncomputable section

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def resolutionVolumeL2 (d : HSMDatum D Ω κ) (n : ℕ) (f : MvPolynomial (Ix κ) ℤ) : ℝ :=
  Real.sqrt (∫ y, ptNorm d.m (Int.castRingHom ℂ) n f (resPt d y) ^ 2 ∂d.dV)

def resolutionVolumeL2Complex (d : HSMDatum D Ω κ) (n : ℕ) (f : MvPolynomial (Ix κ) ℂ) : ℝ :=
  Real.sqrt (∫ y, ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2 ∂d.dV)

def ResolutionSupBound.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ),
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : MvPolynomial (Ix κ) ℂ, f.IsHomogeneous n →
      ∀ z ∈ pts (coordIdeal ℤ d.x),
        ptNorm d.m (RingHom.id ℂ) n f z ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2Complex d n f

theorem ptNorm_map_intCast (m : ConeMetric ℂ (Ix κ)) (n : ℕ) (f : MvPolynomial (Ix κ) ℤ) (z : Ix κ → ℂ) :
    ptNorm m (RingHom.id ℂ) n (map (Int.castRingHom ℂ) f) z = ptNorm m (Int.castRingHom ℂ) n f z := by
  simp [ptNorm, MvPolynomial.map_id]

theorem ResolutionSupBound.toInt (h : ResolutionSupBound.Statement) :
    ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ),
      ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n →
        ∀ z ∈ pts (coordIdeal ℤ d.x),
          ptNorm d.m (Int.castRingHom ℂ) n f z ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2 d n f := by
  intro D Ω _ _ κ _ d
  obtain ⟨C, hC⟩ := h D Ω κ d
  refine ⟨C, fun n hn f hf z hz => ?_⟩
  have := hC n hn (map (Int.castRingHom ℂ) f) (hf.map _) z hz
  simpa only [resolutionVolumeL2Complex, resolutionVolumeL2, ptNorm_map_intCast] using this

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
