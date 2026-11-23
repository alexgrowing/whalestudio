import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
import Formalism.LocalToGlobal.IndefiniteForms.IndefExample
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.FreeLiftMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMatrixMetricMeans

open Module NumberField IsDedekindDomain
open Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.PairingDivisionLocalBalance Formalism.HN

noncomputable section

namespace GlobalTheory.InfinitePlacesProbe

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

def ClauseA (O : FunData K Df) (C b : ℝ) : Prop :=
  ∀ vb : Matrix (Fin O.n) (Fin (Df.dQ Bs.μ0)) K, vb * Df.Pq Bs.μ0 = O.vmu Bs.μ0 →
    htMap (Pi.basisFun K (Fin (Df.dQ Bs.μ0))) (Df.XQ Bs.μ0) (Pi.basisFun K (Fin O.n)) O.X'
      (Matrix.mulVecLin vb) ≤ O.bIPa C b

def ClauseB (S : IndefData Df) (O : FunData K Df) (C b : ℝ) : Prop :=
  ∃ g : InfinitePlace K → ℝ, (∀ v p, Df.Qp Bs.μ0 p ≠ ⊥ → g v ≤ ∑ j, Real.log (S.lam j Bs.μ0 p v)) ∧
    -(3 * C * O.f * O.m * (O.N : ℝ) ^ 2 * Real.log b) ≤ meanInf K g

def scaleTest (O : FunData K Df) (t : InfinitePlace K → ℝ) : FunData K Df := { O with X' := scaleFrame t O.X' }

theorem clauseB_of_lifts [IsTotallyComplex K] {Df' : DefSide Bs} (S : IndefData Df) (S' : IndefData Df') (N : IndefNum Bs)
    (O : FunData K Df) {C b : ℝ} (hC : 0 ≤ C) (hb : 1 ≤ b) (hl : LevelLink S S') (h6 : S'.L6 N)
    (hm : Fintype.card Bs.J ≤ O.m) (hN : ∀ j, -(3 * C * O.f * (O.N : ℝ) ^ 2 * Real.log b) ≤ N.l6 j) :
    ClauseB S O C b := by
  refine ⟨fun _ => _, fun v p _ => ?_, (GlobalTheory.Proof.DualMatrixMetricMeans.meanInf_const _).ge⟩
  have h1 := Real.log_nonneg hb
  have h2 : ∑ _j : Bs.J, -(3 * C * O.f * (O.N : ℝ) ^ 2 * Real.log b) ≤ ∑ j, Real.log (S.lam j Bs.μ0 p v) :=
    Finset.sum_le_sum fun j _ => (hN j).trans (by rw [hl.2.2]; exact h6 j p v)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
  have h3 : (Fintype.card Bs.J : ℝ) ≤ O.m := by exact_mod_cast hm
  have h4 : 0 ≤ 3 * C * O.f * (O.N : ℝ) ^ 2 * Real.log b := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h3 h4]

end GlobalTheory.InfinitePlacesProbe
