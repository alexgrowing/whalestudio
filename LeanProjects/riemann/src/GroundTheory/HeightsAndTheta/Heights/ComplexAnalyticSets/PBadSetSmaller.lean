import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

theorem eval_pullback {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (P : MvPolynomial (Fin d) ℂ)
    (x : Fin n → ℂ) : eval x (pullback A P) = eval (A.mulVec x) P := by
  have h : ∀ i, eval x (linPoly A i) = A.mulVec x i := by
    intro i
    simp [linPoly, Matrix.mulVec, dotProduct, map_sum]
  rw [pullback, aeval_eq_bind₁]
  change eval₂Hom (RingHom.id ℂ) x (bind₁ (linPoly A) P) = eval₂Hom (RingHom.id ℂ) (A.mulVec x) P
  rw [eval₂Hom_bind₁]
  congr 2
  funext i
  exact h i

theorem zeroSet_sup_span {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin n) ℂ) :
    zeroSet (J ⊔ Ideal.span {f}) = zeroSet J ∩ {x | eval x f = 0} := by
  ext x
  have key : ∀ I : Ideal (MvPolynomial (Fin n) ℂ),
      (∀ q ∈ I, eval x q = 0) ↔ I ≤ RingHom.ker (eval x) :=
    fun I => ⟨fun h q hq => (RingHom.mem_ker).2 (h q hq), fun h q hq => (RingHom.mem_ker).1 (h hq)⟩
  simp only [zeroSet, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [key, key, sup_le_iff, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]

theorem BadSetSmaller.proof : BadSetSmaller.Statement := by
  intro n d J A hJ hd hA P hP
  refine ⟨?_, ?_⟩
  · rw [zeroSet_sup_span]
    ext x
    simp [eval_pullback]
  · intro Q hQ
    have := hJ
    set f := pullback A P with hfdef
    have hf : Ideal.Quotient.mk J f ≠ 0 := by
      intro h0
      apply hP
      apply hA.injective
      rw [map_zero]
      simpa [projHom] using h0
    have hnz : Ideal.Quotient.mk J f ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ J) :=
      mem_nonZeroDivisors_of_ne_zero hf
    have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnz
    have hmap : (Ideal.span {f}).map (Ideal.Quotient.mk J) = Ideal.span {Ideal.Quotient.mk J f} := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [← hmap, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup J _), hd] at h1
    have h2 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) ≤
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {f})) :=
      ringKrullDim_le_of_surjective (Ideal.Quotient.factor hQ.1.2)
        (Ideal.Quotient.factor_surjective hQ.1.2)
    exact lt_of_le_of_lt h2 (ENat.WithBot.add_one_le_natCast_iff.mp h1)

end

end GroundTheory.Heights₂.Heights.ComplexSets
