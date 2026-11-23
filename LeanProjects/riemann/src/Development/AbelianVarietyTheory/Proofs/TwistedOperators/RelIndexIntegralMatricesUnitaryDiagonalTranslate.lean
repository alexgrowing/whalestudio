import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIntMat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexUniformizerPowMulIntegersEqSqPowStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexIntegralMatricesDiagonalUniformizerPowStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalUnitaryAntidiagonalFormExponentBalanceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexIntegralMatricesLeftMulUnitaryKUInvarianStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.LatIdx

theorem relIndex_intMat_translate : ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (c : L →+* L) (q : ℕ), IsUnramInv ϖ c q → ∀ (r n : ℕ) (d : Fin r → ℤ) (t : GU c r), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KU c r, ∀ k₂ ∈ KU c r, (GlobalTheory.InertHomIdx.intMat L r n).relIndex ((GlobalTheory.InertHomIdx.intMat L r n).map (GlobalTheory.InertHomIdx.lmul (k₁ * t * k₂).1.1)) = (q ^ 2) ^ (n * (∑ i, max (d i) 0).toNat) := by
  intro L _ _ ϖ c q hq r n d t ht k₁ hk₁ k₂ hk₂

  have hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
    hq.2.2.2.1
  have h0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.zero_ne_coe hv
  have h1 : Valued.v ϖ ≤ 1 := by
    rw [hv, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
    norm_num

  rw [GlobalTheory.T.relIndex_integralMatrices_leftMul_unitary_KU_invariant c r n t k₁ k₂ hk₁ hk₂, ht,
    GlobalTheory.T.relIndex_integralMatrices_diagonal_uniformizer_pow ϖ (q ^ 2) h0 h1 (GlobalTheory.T.relIndex_uniformizer_pow_mul_integers_eq_sq_pow ϖ c q hq) r n d,
    GlobalTheory.T.diagonal_unitary_antidiagonalForm_exponent_balance ϖ c q hq r d t ht]

end GlobalTheory.LatIdx
