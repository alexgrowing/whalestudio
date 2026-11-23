import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped ComplexConjugate
open MeasureTheory MvPolynomial CP

noncomputable section

namespace FSInv

theorem Sesq.proof (hP : PairMk.Statement) : Sesq.Statement := by
  intro N n P Q R hPn hQn hRn c
  have hint : ∀ A B : MvPolynomial (Fin (N + 1)) ℂ, A ∈ H0 N n → B ∈ H0 N n →
      Integrable (fsPair (N := N) n A B) (fsMeasure N) := by
    intro A B hA hB
    have hcont : Continuous (fsPair (N := N) n A B) := by
      rw [ProjTopology.continuous_iff]
      have e : fsPair (N := N) n A B ∘ Projectivization.mk' ℂ =
          fun v : {v : Fin (N + 1) → ℂ // v ≠ 0} =>
            conj (eval v.1 A) * eval v.1 B / ((norm2 v.1 ^ (2 * n) : ℝ) : ℂ) := by
        funext ⟨v, hv⟩
        exact hP N n A B hA hB v hv
      rw [e]
      have hc : Continuous fun v : Fin (N + 1) → ℂ => norm2 v :=
        Real.continuous_sqrt.comp (continuous_finsetSum _ fun j _ =>
          (continuous_norm.comp (continuous_apply j)).pow 2)
      refine Continuous.div ?_ (Complex.continuous_ofReal.comp ((hc.comp continuous_subtype_val).pow _))
        fun v => ?_
      · exact (Complex.continuous_conj.comp ((continuous_eval A).comp continuous_subtype_val)).mul
          ((continuous_eval B).comp continuous_subtype_val)
      · exact_mod_cast (pow_pos (euclideanNorm_pos v.2) _).ne'
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨?_, ?_, ?_⟩
  · have e : fsPair (N := N) n (P + c • Q) R =
        fun x => fsPair n P R x + conj c * fsPair n Q R x := by
      funext x
      simp only [fsPair, map_add, smul_eval, map_mul]
      ring
    rw [l2Inner, e, integral_add (hint P R hPn hRn) ((hint Q R hQn hRn).const_mul _),
      integral_const_mul]
    rfl
  · have e : fsPair (N := N) n R (P + c • Q) =
        fun x => fsPair n R P x + c * fsPair n R Q x := by
      funext x
      simp only [fsPair, map_add, smul_eval]
      ring
    rw [l2Inner, e, integral_add (hint R P hRn hPn) ((hint R Q hRn hQn).const_mul _),
      integral_const_mul]
    rfl
  · have e : fsPair (N := N) n Q P = fun x => conj (fsPair n P Q x) := by
      funext x
      simp only [fsPair, map_div₀, map_mul, Complex.conj_conj, Complex.conj_ofReal]
      ring
    rw [l2Inner, e, integral_conj]
    rfl

end FSInv

end

end GroundTheory.Heights₂.Heights
