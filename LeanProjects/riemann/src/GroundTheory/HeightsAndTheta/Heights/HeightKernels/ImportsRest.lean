import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StandardInnerSingleNe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors

noncomputable section

def S6.LatticeAsBundle.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K)
    (d : (K →+* ℂ) → Fin n → ℝ),
    (∀ x, a x ≠ 0) → (∀ σ x, 0 < d σ x) → (∀ σ x, d (conjugate σ) x = d σ x) →
    ∃ (E : HermitianBundle.{0} K) (L : Fin n → Submodule (𝓞 K) E.carrier),
      DirectSum.IsInternal L ∧ (∀ x, E.rank (L x) = 1) ∧ IsOrthogonalFamily E L ∧
      (∀ x, E.normDegree (L x) = GroundTheory.Heights₂.Heights.normalise K
        (GroundTheory.Heights₂.Heights.subDegree (GroundTheory.Heights₂.Heights.idealLattice a)
          (GroundTheory.Heights₂.Heights.diagMetric d) (fun _ : Fin 1 => (Pi.single x 1 : Fin n → K)))) ∧
      ∀ (m k : ℕ) (b : Fin m → Fin n → K) (c : Fin k → Fin n → K),
        LinearIndependent K (Sum.elim b c) → m + k = n →
        ∃ (E' E'' : HermitianBundle.{0} K), Nonempty (HermitianExtension E' E E'') ∧
          E''.rank ⊤ = k ∧
          E''.normDegree ⊤ = GroundTheory.Heights₂.Heights.normalise K
            (GroundTheory.Heights₂.Heights.quotDegree (GroundTheory.Heights₂.Heights.idealLattice a)
              (GroundTheory.Heights₂.Heights.diagMetric d) b c)

theorem S6.LatticeAsBundle.hypotheses_inhabited :
    let a : Fin 2 → FractionalIdeal (𝓞 ℚ)⁰ ℚ := fun _ => 1
    let d : (ℚ →+* ℂ) → Fin 2 → ℝ := fun _ _ => 1
    let b : Fin 1 → Fin 2 → ℚ := fun _ => Pi.single 0 1
    let c : Fin 1 → Fin 2 → ℚ := fun _ => Pi.single 1 1
    (∀ x, a x ≠ 0) ∧ (∀ σ x, 0 < d σ x) ∧ (∀ σ x, d (conjugate σ) x = d σ x) ∧
      LinearIndependent ℚ (Sum.elim b c) ∧ 1 + 1 = 2 := by
  intro a d b c
  refine ⟨fun _ => one_ne_zero, fun _ _ => one_pos, fun _ _ => rfl, ?_, rfl⟩
  have h : Sum.elim b c = (Pi.basisFun ℚ (Fin 2)) ∘ finSumFinEquiv := by
    funext i
    rcases i with i | i <;> fin_cases i
    · simp [b, Pi.basisFun_apply]
      rfl
    · simp [c, Pi.basisFun_apply]
      rfl
  rw [h]
  exact (Pi.basisFun ℚ (Fin 2)).linearIndependent.comp _ finSumFinEquiv.injective

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
