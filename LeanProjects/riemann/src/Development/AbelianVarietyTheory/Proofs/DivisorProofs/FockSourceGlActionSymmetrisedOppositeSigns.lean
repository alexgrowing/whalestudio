import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColDerApply

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockOpp

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

theorem raiO_mul_lowO_apply {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (h : ∀ i j, ε' i ≠ ε j) (i : Fin b) (j k : Fin a) (P : PolF D b a) :
    (raiO τ ε ε' i j * lowO τ ε ε' i k) P =
      -(X (τ, i, k) * pderiv (τ, i, j) P) - (if j = k then P else 0) := by
  classical
  have hs : sgn (ε j) * sgn (ε k) = 1 := by
    have h1 := h i j
    have h2 := h i k
    unfold sgn
    cases hi : ε' i <;> cases hj : ε j <;> cases hk : ε k <;> simp_all
  unfold raiO lowO
  rw [if_neg (h i j), if_neg (h i k), smul_mul_smul_comm, hs, one_smul]
  simp only [Module.End.mul_apply, LinearMap.neg_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe,
    Derivation.leibniz, smul_eq_mul, pderiv_X, Pi.single_apply, Prod.mk.injEq, true_and]
  by_cases hjk : j = k
  · subst hjk
    simp only [if_true, mul_one]
    ring
  · simp [hjk, Ne.symm hjk]

theorem fockS_of_opposite {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (Y : Matrix (Fin a) (Fin a) ℂ) (h : ∀ i j, ε' i ≠ ε j) :
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ε ε' Y =
      -(GlobalTheory.ColLie.colDer τ Y.transpose : Module.End ℂ (PolF D b a)) - (((b : ℂ) / 2) * Y.trace) • 1 := by
  classical
  refine LinearMap.ext fun P => ?_
  have key : ∀ (i : Fin b) (j k : Fin a),
      (raiO τ ε ε' i j * lowO τ ε ε' i k + if j = k then (1 / 2 : ℂ) • 1 else 0 : Module.End ℂ (PolF D b a)) P =
        -(X (τ, i, k) * pderiv (τ, i, j) P) - (if j = k then (1 / 2 : ℂ) else 0) • P := by
    intro i j k
    rw [LinearMap.add_apply, raiO_mul_lowO_apply τ ε ε' h]
    by_cases hjk : j = k
    · simp only [hjk, if_true, LinearMap.smul_apply, Module.End.one_apply]
      module
    · simp [hjk]
  have htr : ∑ j, ∑ k, Y j k • ∑ _i : Fin b, (if j = k then (1 / 2 : ℂ) else 0) • P =
      (((b : ℂ) / 2) * Y.trace) • P := by
    simp only [← Finset.sum_smul, smul_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.trace, Matrix.diag, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have hcol : (GlobalTheory.ColLie.colDer τ Y.transpose : Module.End ℂ (PolF D b a)) P =
      ∑ j, ∑ k, Y j k • ∑ i : Fin b, (X (τ, i, k) * pderiv (τ, i, j) P : PolF D b a) := by
    rw [GlobalTheory.ColLie.colDer_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.smul_sum]
    rfl
  rw [LinearMap.sub_apply, LinearMap.neg_apply, hcol, LinearMap.smul_apply, Module.End.one_apply, ← htr]
  unfold fockS
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, key, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    smul_sub, smul_neg]

end GlobalTheory.FockOpp
