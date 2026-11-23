import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Assembly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

variable {T T₂ : Type} [Fintype T] [DecidableEq T] [Fintype T₂]

def intCoordSubst (A : Matrix T T₂ ℤ) : MRing (dualBlocks T₂) →ₐ[ℤ] MRing (dualBlocks T) :=
  aeval fun p => ∑ t, C (A t p.2) * X (⟨(), t⟩ : Σ _ : Unit, T)

def intCoordPt (A : Matrix T T₂ ℤ) (z : (Σ _ : Unit, T) → ℂ) : (Σ _ : Unit, T₂) → ℂ :=
  fun p => ∑ t, z ⟨(), t⟩ * (A t p.2 : ℂ)

theorem intCoordPt_ne_zero {A : Matrix T T₂ ℤ} (hA : ∃ B : Matrix T₂ T ℤ, A * B = 1)
    {z : (Σ _ : Unit, T) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, intCoordPt A z ⟨k, i⟩ ≠ 0 := by
  classical
  obtain ⟨B, hB⟩ := hA
  rintro ⟨⟩
  obtain ⟨t, ht⟩ := hz ()
  by_contra h
  push Not at h
  apply ht
  have h1 : ∀ t', (((A * B) t' t : ℤ) : ℂ) = ∑ s, (A t' s : ℂ) * (B s t : ℂ) := by
    intro t'
    simp [Matrix.mul_apply]
  have key : z ⟨(), t⟩ = ∑ s, intCoordPt A z ⟨(), s⟩ * (B s t : ℂ) := by
    simp only [intCoordPt, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, ← h1, hB, Matrix.one_apply]
    simp
  rw [key]
  exact Finset.sum_eq_zero fun s _ => by rw [h s, zero_mul]

def intCoordLine (A : Matrix T T₂ ℤ) (hA : ∃ B : Matrix T₂ T ℤ, A * B = 1)
    (L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T₂)) : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T) where
  a := L.a
  h z := L.h (intCoordPt A z)
  pos z hz := L.pos _ (intCoordPt_ne_zero hA hz)
  smul c z hc := by
    have hz : intCoordPt A (fun p => c p.1 * z p) = fun p => c p.1 * intCoordPt A z p := by
      funext p
      obtain ⟨⟨⟩, s⟩ := p
      simp only [intCoordPt, Finset.mul_sum, mul_assoc]
    rw [hz, L.smul c _ hc]

def IntCoordChange.Statement : Prop :=
  ∀ (T T₂ : Type) [Fintype T] [DecidableEq T] [Fintype T₂] [DecidableEq T₂] (A : Matrix T T₂ ℤ)
    (B : Matrix T₂ T ℤ) (hAB : A * B = 1), B * A = 1 → ∀ (II : IntersectionSystem),
    IsIntersectionSystem II → ∀ (P : Ideal (MRing (dualBlocks T₂))) (n : ℕ)
    (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T₂)), 1 ≤ n → IsArithVar P n → (∀ j, IsSmoothHerm (L j)) →
    II Unit (dualBlocks T) (P.map (intCoordSubst A)) n (fun j => intCoordLine A ⟨B, hAB⟩ (L j)) =
      II Unit (dualBlocks T₂) P n L

example : (-1 : Matrix Unit Unit ℤ) * (-1) = 1 ∧ (-1 : Matrix Unit Unit ℤ) * (-1) = 1 ∧ 1 ≤ 1 ∧
    IsArithVar (dualIdeal dualBasisStandard) 1 ∧
    IsSmoothHerm (dualLine (HermLattice.standard ℚ 1) dualBasisStandard dualEmbMatrix_standard_bijective) :=
  ⟨by simp, by simp, le_rfl, DualArithVar.full ℚ 1 _ Unit dualBasisStandard le_rfl,
    (DualLineSemipositive.proof ℚ 1 _ Unit dualBasisStandard _).1⟩

example : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks Unit) :=
  intCoordLine (-1 : Matrix Unit Unit ℤ) ⟨-1, by simp⟩
    (dualLine (HermLattice.standard ℚ 1) dualBasisStandard dualEmbMatrix_standard_bijective)

example : intCoordSubst (-1 : Matrix Unit Unit ℤ) (X ⟨(), ()⟩) = -X ⟨(), ()⟩ := by
  simp [intCoordSubst]

end

end GroundTheory.Heights₂.Heights
