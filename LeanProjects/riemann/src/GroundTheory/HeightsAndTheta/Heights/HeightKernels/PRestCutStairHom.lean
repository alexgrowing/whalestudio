import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem RestCutStairHom.proof : RestCutStairHom.Statement := by
  intro f N
  have hsum : (∑ i : Fin N, (i : ℕ)) = N * (N - 1) / 2 :=
    (Nat.div_eq_of_eq_mul_left (by norm_num) (KRest.sum_fin_val_mul_two N).symm).symm
  have hinner : ∀ τ : Fin f,
      (∏ i : Fin N, (X (τ, i) : RestTerms.RootRing f N) ^ (i : ℕ)).IsHomogeneous
        (∑ i : Fin N, (i : ℕ)) :=
    fun τ => IsHomogeneous.prod _ _ _ fun i _ => isHomogeneous_X_pow _ _
  have h := IsHomogeneous.prod (Finset.univ : Finset (Fin f)) _ _ fun τ _ => hinner τ
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  unfold restStair RestTerms.topDegree
  rw [← hsum]
  exact h

end GroundTheory.Heights₂.Heights
