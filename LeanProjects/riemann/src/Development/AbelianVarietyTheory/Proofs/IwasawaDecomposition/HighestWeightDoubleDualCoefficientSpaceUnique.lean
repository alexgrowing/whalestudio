import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NablaSqUpperEigenvectorWeightEqHighestStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpecialisationCoefficientSpaceToDualWeylStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HighestWeightDoubleDualUpperTriangularEigenvectoStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.AlgWtF.DDHw

theorem dd_hw_unique : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [CharZero K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb → ∀ (τ₀ : ι) (mu : Fin n → ℤ),
      NX.HWAtF (IsCMField.complexConj L : L →+* L) (GlobalTheory.AlgWtF.wtRepF emb lam).dual (emb τ₀) mu → mu = (lam τ₀).w := by
  intro L _ _ _ n ι _ K _ _ emb lam hd τ₀ mu h
  classical
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  obtain ⟨w, hwV, hw0, hB⟩ := GlobalTheory.T.highestWeight_doubleDual_upperTriangular_eigenvector L n ι K emb lam hd τ₀ mu h
  obtain ⟨φ, hφ0, hφV, hφA⟩ := GlobalTheory.T.exists_specialisation_coefficientSpace_to_dualWeyl K n ι lam τ₀ w hwV hw0
  refine GlobalTheory.T.nablaSq_upperEigenvector_weight_eq_highest K n (lam τ₀) mu (φ w) (hφV w hwV) hφ0 fun B hBt => ?_
  have hc0 : detPow K n B (lam τ₀).detShift ≠ 0 := by
    rw [detPow]; exact Units.ne_zero _
  rw [sqAct, ← hφA, hB B hBt, map_smul, smul_smul, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

end GlobalTheory.AlgWtF.DDHw
