import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSpaceStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.DefiniteCartan

open Matrix

theorem re_pos_of_hasSig {n r : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r 0) (x : Fin n → ℂ)
    (hx : x ≠ 0) : 0 < (x ⬝ᵥ M *ᵥ star x).re := by
  obtain ⟨hr, A, hA⟩ := h
  have h1 : Aᵀ * M * A.map star = 1 := by
    rw [hA]; ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  let e : Fin r ⊕ Fin 0 ≃ Fin n := (Equiv.sumEmpty (Fin r) (Fin 0)).trans (finCongr (by omega))
  have h2 : A * (M * A.map star)ᵀ = 1 := by
    have h3 : (M * A.map star) * Aᵀ = 1 :=
      (Matrix.mul_eq_one_comm_of_equiv e).1 (by rw [← Matrix.mul_assoc]; exact h1)
    have h4 := congrArg Matrix.transpose h3
    simpa [Matrix.transpose_mul] using h4
  obtain ⟨z, hxz⟩ : ∃ z, x = A *ᵥ z := ⟨(M * A.map star)ᵀ *ᵥ x, by rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]⟩
  have hz0 : z ≠ 0 := by
    intro h0; apply hx; rw [hxz, h0, Matrix.mulVec_zero]
  have hstar : star (A *ᵥ z) = A.map star *ᵥ star z := by
    ext i; simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]
  have key : x ⬝ᵥ M *ᵥ star x = z ⬝ᵥ star z := by
    rw [hxz, hstar, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose A z, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, ← Matrix.mul_assoc, h1, Matrix.vecMul_one]
  rw [key, dotProduct, Complex.re_sum]
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hz0
  refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
  · simp only [Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  · simp only [Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_pos.2 hi

theorem eq_one_of_hasSig {n r : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (hM : HasSig M r 0) (hθ : IsCartan M θ) :
    θ = 1 := by
  obtain ⟨hsq, -, hpos⟩ := hθ
  have hfix : ∀ y : Fin n → ℂ, θ *ᵥ y = y := by
    intro y
    by_contra hne
    have hx : y - θ *ᵥ y ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    have hθx : θ *ᵥ (y - θ *ᵥ y) = -(y - θ *ᵥ y) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hsq, Matrix.one_mulVec, neg_sub]
    have h1 := hpos _ hx
    have h2 := re_pos_of_hasSig hM _ hx
    rw [hθx, neg_dotProduct, Complex.neg_re] at h1
    linarith
  exact Matrix.ext_of_mulVec_single fun j => by rw [hfix, Matrix.one_mulVec]

end GlobalTheory.DefiniteCartan

namespace GlobalTheory

end GlobalTheory
