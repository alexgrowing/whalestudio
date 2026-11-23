import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.EisCT

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E)

theorem stabL_one_transv : StabL σ J x 1 := ⟨1, by simp⟩

theorem stabL_mul_transv {g h : GAd σ J} (hg : StabL σ J x g) (hh : StabL σ J x h) : StabL σ J x (g * h) := by
  obtain ⟨a, ha⟩ := hg
  obtain ⟨b, hb⟩ := hh
  refine ⟨b * a, ?_⟩
  rw [map_mul, Units.val_mul, Matrix.mul_assoc, hb, Matrix.mul_smul, ha, smul_smul, Units.val_mul]

theorem stabL_inv_transv {g : GAd σ J} (hg : StabL σ J x g) : StabL σ J x g⁻¹ := by
  obtain ⟨a, ha⟩ := hg
  refine ⟨a⁻¹, ?_⟩
  have h1 : (matHom _ σ J g⁻¹).1 * ((matHom _ σ J g).1 * adMat F x) = adMat F x := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul]
  rw [ha, Matrix.mul_smul] at h1
  calc (matHom _ σ J g⁻¹).1 * adMat F x
      = (a⁻¹).1 • (a.1 • ((matHom _ σ J g⁻¹).1 * adMat F x)) := by
        rw [smul_smul, Units.inv_mul, one_smul]
    _ = _ := by rw [h1]

end

theorem exists_isTransv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E), ∃ T, GlobalTheory.EisCT.IsTransv σ J x T := by
  intro F E _ _ _ _ _ σ n J x
  let S : Setoid (ratPts σ J) :=
    { r := fun γ t => StabL σ J x (γ * t⁻¹ : ratPts σ J).1
      iseqv :=
        { refl := fun γ => by
            rw [mul_inv_cancel]
            exact stabL_one_transv σ J x
          symm := fun {a b} h => by
            have h2 := stabL_inv_transv σ J x h
            have e : (b * a⁻¹ : ratPts σ J) = (a * b⁻¹)⁻¹ := by group
            rw [e]
            exact h2
          trans := fun {a b c} h1 h2 => by
            have h3 := stabL_mul_transv σ J x h1 h2
            have e : (a * c⁻¹ : ratPts σ J) = (a * b⁻¹) * (b * c⁻¹) := by group
            rw [e]
            exact h3 } }
  refine ⟨Set.range (Quotient.out (s := S)), fun γ => ⟨(Quotient.mk S γ).out, ⟨⟨_, rfl⟩, ?_⟩, ?_⟩⟩
  · exact S.symm (Quotient.mk_out (s := S) γ)
  · rintro t ⟨⟨q, rfl⟩, ht⟩
    have h : Quotient.mk S γ = Quotient.mk S q.out := Quotient.sound (s := S) ht
    rw [h, Quotient.out_eq]

end GlobalTheory.EisCT
