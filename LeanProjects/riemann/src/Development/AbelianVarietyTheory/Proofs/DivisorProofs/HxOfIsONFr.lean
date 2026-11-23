import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HermFormDiagonalEq
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem hx_of_isONFr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r g n : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → Even n → ∀ x : Frame X.Ψ r, IsONFr X x → x ∈ X.dom ∧ IsUnitFr X x ∧ ∀ z w : Fin g → ℂ, hx X bas idx x z w = ∑ j, (X.c (idx j).1 : ℂ) * z j * conj (w j) := by
  intro E _ _ _ r g n X bas idx hs _ x ho
  have hsg : ∀ a : ℕ, FD.sgn X.p0 a = 1 ∨ FD.sgn X.p0 a = -1 := fun a => by
    unfold FD.sgn; split_ifs <;> simp
  have e (τ : X.Ψ) (i : Fin (r + 1)) : dmin X.Gm x τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [ho τ, sgnM, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    push_cast
    exact Fin.prod_univ_eq_prod_range (fun a => ((FD.sgn X.p0 a : ℝ) : ℂ)) (i : ℕ)
  have h0 (i : ℕ) : psgn X.p0 i ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun a _ => by rcases hsg a with h | h <;> rw [h] <;> norm_num
  have hd : x ∈ X.dom := by
    refine fun τ => ⟨fun h => ?_, fun i => ?_⟩
    · have h1 : FD.gram τ.1 X.Gm (mat x τ) =
          (mat x τ)ᵀ * X.Gm.map τ.1 * (mat x τ).map (starRingEnd ℂ) := by
        ext a b
        simp only [FD.gram, hermC, FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
          Matrix.map_apply, Finset.sum_mul]
        exact Finset.sum_comm
      have h2 := congrArg Matrix.det (h1.symm.trans (ho τ))
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul, zero_mul, sgnM,
        Matrix.det_diagonal] at h2
      refine Finset.prod_ne_zero_iff.2 (fun a _ => ?_) h2.symm
      rcases hsg a with h | h <;> rw [h] <;> norm_num
    · rw [e, Complex.ofReal_re]
      exact mul_self_pos.2 (h0 _)
  refine ⟨hd, fun τ i => ?_, (GlobalTheory.Dict.hx_ortho E r X g bas idx hs x hd ho).1⟩
  rw [e, psgn]
  push_cast
  rw [norm_prod]
  exact Finset.prod_eq_one fun a _ => by rcases hsg a with h | h <;> rw [h] <;> simp

end GlobalTheory.AdTh
