import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IncMatTransposeConjTranspose
open scoped TensorProduct Matrix
open NumberField Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.FockIncl GlobalTheory.FockInclK

noncomputable section

namespace GlobalTheory.FockInclAct

variable {P Q R S : ℕ} (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1))

theorem skipLine_injective :
    Function.Injective (Prod.map id (skipIx r₀ s₀) : Ln P Q R S → Ln P Q (R + 1) (S + 1)) :=
  Function.injective_id.prodMap (skipIx_injective r₀ s₀)

theorem linePos_skip (a : Ix P Q) (c : Ix R S) :
    linePos ((a, skipIx r₀ s₀ c) : Ln P Q (R + 1) (S + 1)) = linePos ((a, c) : Ln P Q R S) := by
  rcases a with a | a <;> rcases c with c | c <;> rfl

theorem polIncl_pderiv (a : Ix P Q) (c : Ix R S) (f : Pol P Q R S) :
    polIncl P Q r₀ s₀ (MvPolynomial.pderiv (a, c) f) =
      MvPolynomial.pderiv (a, skipIx r₀ s₀ c) (polIncl P Q r₀ s₀ f) :=
  (MvPolynomial.pderiv_rename (skipLine_injective r₀ s₀) (a, c) f).symm

theorem polIncl_X (a : Ix P Q) (c : Ix R S) :
    polIncl P Q r₀ s₀ (MvPolynomial.X (a, c)) = MvPolynomial.X (a, skipIx r₀ s₀ c) :=
  MvPolynomial.rename_X _ _

theorem polIncl_lowB (a : Ix P Q) (c : Ix R S) (f : Pol P Q R S) :
    polIncl P Q r₀ s₀ (lowB (a, c) f) = lowB (a, skipIx r₀ s₀ c) (polIncl P Q r₀ s₀ f) := by
  unfold lowB
  rw [linePos_skip]
  split_ifs
  · exact polIncl_pderiv r₀ s₀ a c f
  · simp only [LinearMap.mulLeft_apply, map_mul, polIncl_X]

theorem polIncl_raiB (a : Ix P Q) (c : Ix R S) (f : Pol P Q R S) :
    polIncl P Q r₀ s₀ (raiB (a, c) f) = raiB (a, skipIx r₀ s₀ c) (polIncl P Q r₀ s₀ f) := by
  unfold raiB
  rw [linePos_skip]
  split_ifs
  · simp only [LinearMap.mulLeft_apply, map_mul, polIncl_X]
  · simp only [LinearMap.neg_apply, map_neg]
    exact congrArg Neg.neg (polIncl_pderiv r₀ s₀ a c f)

theorem polIncl_omE (a : Ix P Q) (c d : Ix R S) (f : Pol P Q R S) :
    polIncl P Q r₀ s₀ (omE (a, c) (a, d) f) =
      omE (a, skipIx r₀ s₀ c) (a, skipIx r₀ s₀ d) (polIncl P Q r₀ s₀ f) := by
  unfold omE
  simp only [LinearMap.add_apply, Module.End.mul_apply, map_add, polIncl_raiB, polIncl_lowB, Prod.mk.injEq, true_and,
    (skipIx_injective r₀ s₀).eq_iff]
  split_ifs <;> simp

theorem extMat_Eab (c d : Ix R S) : extMat r₀ s₀ (Eab c d) = Eab (skipIx r₀ s₀ c) (skipIx r₀ s₀ d) := by
  ext a b
  rw [extMat_apply, Finset.sum_eq_single c, Finset.sum_eq_single d]
  · simp only [Eab, Matrix.single_apply]
    by_cases ha : a = skipIx r₀ s₀ c <;> by_cases hb : b = skipIx r₀ s₀ d <;> simp [ha, hb, eq_comm]
  · intro e _ he
    simp [Eab, Matrix.single_apply, Ne.symm he]
  · simp
  · intro e _ he
    refine Finset.sum_eq_zero fun g _ => ?_
    simp [Eab, Matrix.single_apply, Ne.symm he]
  · simp

theorem polIncl_comp_fockAct2 (P Q R S : ℕ) (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) (Y : Mat R S) :
    (polIncl P Q r₀ s₀).toLinearMap ∘ₗ fockAct2 P Q R S Y =
      fockAct2 P Q (R + 1) (S + 1) (extMat r₀ s₀ Y) ∘ₗ (polIncl P Q r₀ s₀).toLinearMap := by
  have hY : Y = ∑ c, ∑ d, Y c d • Eab c d := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    simp [Eab, Matrix.smul_single]
  have hE : extMat r₀ s₀ Y = ∑ c, ∑ d, Y c d • Eab (skipIx r₀ s₀ c) (skipIx r₀ s₀ d) := by
    conv_lhs => rw [hY]
    simp only [← extMat_Eab, extMat, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  refine LinearMap.ext fun f => ?_
  rw [hE]
  conv_lhs => rw [hY]
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    fockAct2_Eab, polIncl_omE]

end GlobalTheory.FockInclAct
