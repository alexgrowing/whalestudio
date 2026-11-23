import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

noncomputable section

namespace GlobalTheory.SphLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mat_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

theorem mat_inv_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

def locU (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) : Subgroup (UA σ W.J) where
  carrier := UAt σ W (evFin F v)
  one_mem' := fun u _ => by simp [mat_one]
  mul_mem' := by
    intro g h hg hh u hu
    have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
      rw [mat_mul, sub_mul, one_mul, sub_add_sub_cancel]
    show u • (mat (g * h) - 1) = 0
    rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]
  inv_mem' := by
    intro g hg u hu
    have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by
      rw [mul_sub, mat_inv_mul, mul_one, neg_sub]
    show u • (mat g⁻¹ - 1) = 0
    rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]

def locK (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) : Subgroup (UA σ W.J) where
  carrier := KAt σ W v
  one_mem' := one_mem_KAt σ W v
  mul_mem' := by
    intro g h hg hh
    refine ⟨(locU σ W v).mul_mem hg.1 hh.1, fun z hz => ⟨?_, ?_⟩⟩
    · rw [mat_mul, ← Matrix.mulVec_mulVec]
      exact (hg.2 _ (hh.2 z hz).1).1
    · rw [mul_inv_rev, mat_mul, ← Matrix.mulVec_mulVec]
      exact (hh.2 _ (hg.2 z hz).2).2
  inv_mem' := by
    intro g hg
    refine ⟨(locU σ W v).inv_mem hg.1, fun z hz => ⟨(hg.2 z hz).2, ?_⟩⟩
    rw [inv_inv]
    exact (hg.2 z hz).1

theorem mem_locK {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F} {g : UA σ W.J} :
    g ∈ locK σ W v ↔ g ∈ KAt σ W v := Iff.rfl

theorem locK_le_locU (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) : locK σ W v ≤ locU σ W v :=
  fun _ hg => hg.1

end GlobalTheory.SphLine

end
