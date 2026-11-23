import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G

abbrev projPts {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (P : Ideal (Geo.MRing ι)) :=
  Quot fun z z' : Geo.mcPts P ↦
    ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ (z' : (Σ k, ι k) → ℂ) = fun p ↦ c p.1 * (z : (Σ k, ι k) → ℂ) p

theorem degC_eq_card_projPts {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (P : Ideal (Geo.MRing ι)) : Geo.degC P = Nat.card (projPts P) := rfl

def PtsIntegralPoints.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [Nonempty K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (Geo.MRing ι)) (g : ((Σ k, ι k) → ℂ) → ℝ),
    Finite (projPts P) →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → z ∈ Geo.mcPts P →
      g (fun p ↦ c p.1 * z p) = g z) →
    Geo.ptsIntegral P (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) g =
      ∑ᶠ q : projPts P, g (Quot.out q : Geo.mcPts P)

example : Finite (projPts (ι := blockIdx (fun _ : Unit ↦ 1)) (orbitIdeal samplePoint)) ∧
    ∀ (c : Unit → ℂ) (z : Coord (fun _ : Unit ↦ 1) → ℂ), (∀ k, c k ≠ 0) →
      z ∈ Geo.mcPts (ι := blockIdx (fun _ : Unit ↦ 1)) (orbitIdeal samplePoint) →
      (fun w : Coord (fun _ : Unit ↦ 1) → ℂ ↦ ‖w ⟨(), 0⟩‖ / ‖w ⟨(), 1⟩‖) (fun p ↦ c p.1 * z p) =
        (fun w : Coord (fun _ : Unit ↦ 1) → ℂ ↦ ‖w ⟨(), 0⟩‖ / ‖w ⟨(), 1⟩‖) z := by
  refine ⟨(Nat.card_pos_iff.mp (OrbitDegree.full Unit _ samplePoint samplePoint_blockNonzero)).2,
    fun c z hc _ ↦ ?_⟩
  simp only [norm_mul]
  exact mul_div_mul_left _ _ (norm_ne_zero_iff.mpr (hc ()))

end GroundTheory.Heights₂.Heights
