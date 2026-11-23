import Formalism.SharpRestriction.GrowthBounds.RootWeights.V2conSumApply

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem v2con_bracket {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a b c d : Fin n) :
    ⁅letterPolarizationDerivation R LL S a b, letterPolarizationDerivation R LL S c d⁆ =
      (if b = c then letterPolarizationDerivation R LL S a d else 0) - (if d = a then letterPolarizationDerivation R LL S c b else 0) := by
  classical
  apply MvPolynomial.derivation_ext
  rintro ⟨l, e⟩
  rw [Derivation.commutator_apply, Derivation.sub_apply]
  have h1 : (if b = c then letterPolarizationDerivation R LL S a d else 0) (X (l, e)) =
      if b = c then letterPolarizationDerivation R LL S a d (X (l, e)) else 0 := by split_ifs <;> simp
  have h2 : (if d = a then letterPolarizationDerivation R LL S c b else 0) (X (l, e)) =
      if d = a then letterPolarizationDerivation R LL S c b (X (l, e)) else 0 := by split_ifs <;> simp
  rw [h1, h2]
  simp only [v2con_der_X]
  have k5 : (c = b) = (b = c) := propext eq_comm
  have k6 : (a = d) = (d = a) := propext eq_comm
  by_cases hS : l ∈ S
  · by_cases hv : LL.vec l = true
    · simp only [hS, hv, if_true]
      by_cases h3 : e = d <;> by_cases h4 : e = b <;> by_cases h5 : b = c <;> by_cases h6 : d = a <;>
        simp_all [v2con_der_X]
    · simp only [hS, hv, if_true]
      by_cases h3 : e = c <;> by_cases h4 : e = a <;> by_cases h5 : b = c <;> by_cases h6 : d = a <;>
        simp_all [v2con_der_X]
  · simp [hS]

theorem polynomial_operators_gl_relations : PolynomialOperatorsGLRelations := by
  intro R _ ι _ LL n S a b c d
  apply LinearMap.ext
  intro F
  have h := congrArg (fun D : Derivation R (MvPolynomial (ι × Fin n) R) (MvPolynomial (ι × Fin n) R) => D F)
    (v2con_bracket (R := R) LL S a b c d)
  simp only [Derivation.commutator_apply, Derivation.sub_apply] at h
  simp only [glOps, LinearMap.sub_apply, Module.End.mul_apply, v2con_glAct_eq]
  rw [h]
  congr 1
  · split_ifs <;> simp [v2con_glAct_eq]
  · split_ifs <;> simp [v2con_glAct_eq]

end Formalism.MainNotions.G.GLWeightTheory
