import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.LineStabReps

theorem exists_reps : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E),
    ∃ T : Set (ratPts σ J), ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ l : (AF F ⊗[F] E)ˣ,
      (matHom _ σ J (γ * t⁻¹ : ratPts σ J).1).1 * adMat F x = l.1 • adMat F x := by
  intro F E _ _ _ _ _ σ n J x
  classical
  let H : Subgroup (ratPts σ J) :=
    { carrier := {p | ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p.1).1 * adMat F x = l.1 • adMat F x}
      one_mem' := ⟨1, by simp⟩
      mul_mem' := by
        rintro p q ⟨l, hl⟩ ⟨l', hl'⟩
        refine ⟨l' * l, ?_⟩
        have e : (matHom _ σ J (p * q).1).1 = (matHom _ σ J p.1).1 * (matHom _ σ J q.1).1 := by
          simp [Subgroup.coe_mul, map_mul, Units.val_mul]
        rw [e, Matrix.mul_assoc, hl', Matrix.mul_smul, hl, smul_smul, Units.val_mul]
      inv_mem' := by
        rintro p ⟨l, hl⟩
        refine ⟨l⁻¹, ?_⟩
        have e : (matHom _ σ J (p⁻¹).1).1 = ((matHom _ σ J p.1)⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1 := by
          simp [Subgroup.coe_inv, map_inv]
        rw [e]
        have h1 : ((matHom _ σ J p.1)⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1 * ((matHom _ σ J p.1).1 * adMat F x) = adMat F x := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
        rw [hl, Matrix.mul_smul] at h1
        calc _ = (l⁻¹).1 • (l.1 • (((matHom _ σ J p.1)⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1 * adMat F x)) := by
                rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
          _ = _ := by rw [h1] }
  refine ⟨Set.range (fun q : Quotient (QuotientGroup.rightRel H) => q.out), fun γ => ?_⟩
  have key : ∀ t : ratPts σ J, γ * t⁻¹ ∈ H ↔ (Quotient.mk _ t : Quotient (QuotientGroup.rightRel H)) = Quotient.mk _ γ := by
    intro t
    rw [Quotient.eq, QuotientGroup.rightRel_apply]
  refine ⟨(Quotient.mk (QuotientGroup.rightRel H) γ).out, ⟨⟨_, rfl⟩, (key _).2 (Quotient.out_eq _)⟩, ?_⟩
  rintro t ⟨⟨q, rfl⟩, ht⟩
  have h2 := (key _).1 ht
  rw [Quotient.out_eq] at h2
  rw [h2]

end GlobalTheory.LineStabReps
