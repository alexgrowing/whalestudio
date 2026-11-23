import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorPolyMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetAddOneSubEqSumQminorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracedQminorComatrixTruncatedInverseStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonicStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

namespace GlobalTheory.CapelliGelfand

open Formalism.REAL Finset

theorem epow_eq_pow {B : Type} [Ring B] {n : ℕ} (E : Fin n → Fin n → B) (m : ℕ) (a b : Fin n) :
    epow E m a b = (Matrix.of E ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [epow, Matrix.one_apply]
  | succ m ih => simp [epow, pow_succ, Matrix.mul_apply, ih]

theorem etr_succ_eq_gelfA {B : Type} [Ring B] {n : ℕ} (E : Fin n → Fin n → B) (k : ℕ) :
    etr E (k + 1) = GlobalTheory.SmoothForms.gelfA E k := by
  rw [GlobalTheory.SmoothForms.gelfA_eq_sum_pow]; simp [etr, epow_eq_pow]

theorem etr_mem_adjoin_qdet (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A)
    (hX : GlRel X) (N : ℕ) : etr X N ∈ Algebra.adjoin ℂ (Set.range (qdet X)) := by
  set S := Algebra.adjoin ℂ (Set.range (qdet X)) with hS
  have hq : ∀ u, qdet X u ∈ S := fun u => Algebra.subset_adjoin ⟨u, rfl⟩
  cases n with
  | zero => simp [etr]
  | succ m =>
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      obtain ⟨c, hc1, hc⟩ := GlobalTheory.T.exists_monic_poly_eq_qdet A (m + 1) X
      have hmin : ∀ i j : Fin (m + 1), ∃ c' : ℕ → A, ∀ w : ℂ,
          qminor X (Fin.succAbove j) (Fin.succAbove i) w = ∑ d ∈ range (m + 1), w ^ d • c' d := by
        intro i j
        obtain ⟨c', hc'⟩ := GlobalTheory.qminor_polyMap A (m + 1) m X (Fin.succAbove j) (Fin.succAbove i) 0
        exact ⟨c', fun w => by simpa using hc' w⟩
      choose cm hcm using hmin
      let Rs : ℂ → A := fun w => ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor X (Fin.succAbove j) (Fin.succAbove i) w
          * epow X (N + 1) j i
      let Rc : ℕ → A := fun d => ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * cm i j d * epow X (N + 1) j i
      have hR : ∀ w : ℂ, Rs w = ∑ d ∈ range (m + 1), w ^ d • Rc d := by
        intro w
        simp only [Rs, Rc, hcm, mul_sum, sum_mul, smul_sum, mul_smul_comm, smul_mul_assoc]
        conv_lhs => enter [2, x]; rw [sum_comm]
        rw [sum_comm]
      let f : ℂ → A := fun u => qdet X u * etr X N - Rs u
      let a : ℕ → A := fun i => c i * etr X N - if i < m + 1 then Rc i else 0
      have hf : ∀ u, f u = ∑ i ∈ range (m + 1 + 1), u ^ i • a i := by
        intro u
        simp only [f, a, hc u, hR u, sum_mul, smul_mul_assoc, smul_sub, sum_sub_distrib]
        congr 1
        rw [sum_range_succ _ (m + 1), if_neg (lt_irrefl _), smul_zero, add_zero]
        exact sum_congr rfl fun i hi => by rw [if_pos (mem_range.mp hi)]
      have hmem : ∀ u, f u ∈ S := by
        intro u
        have h1 := GlobalTheory.T.traced_qminor_comatrix_truncated_inverse A m X hX u N
        rw [← GlobalTheory.T.qdet_add_one_sub_eq_sum_qminor', sum_range_succ, Nat.sub_self, pow_zero, mul_one, mul_add] at h1
        have key : algebraMap ℂ A ((-1) ^ N) * f u = algebraMap ℂ A ((u - m) ^ (N + 1)) * (qdet X (u + 1) - qdet X u)
            - qdet X u * ∑ k ∈ range N, algebraMap ℂ A ((-1) ^ k * (u - m) ^ (N - k)) * etr X k := by
          simp only [f]
          rw [mul_sub, ← mul_assoc, Algebra.commutes, mul_assoc, sub_eq_sub_iff_add_eq_add, h1]
          abel
        have hm : algebraMap ℂ A ((-1) ^ N) * f u ∈ S := by
          rw [key]
          refine sub_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (sub_mem (hq _) (hq _)))
            (mul_mem (hq _) (sum_mem fun k hk => mul_mem (Subalgebra.algebraMap_mem _ _) (ih k (mem_range.mp hk))))
        have : f u = algebraMap ℂ A ((-1) ^ N) * (algebraMap ℂ A ((-1) ^ N) * f u) := by
          rw [← mul_assoc, ← map_mul, ← mul_pow, neg_one_mul, neg_neg, one_pow, map_one, one_mul]
        rw [this]
        exact mul_mem (Subalgebra.algebraMap_mem _ _) hm
      have htop := GlobalTheory.LeviHC.coeff_mem_span hf (i := m + 1) (Nat.lt_succ_self _)
      have ha : a (m + 1) = etr X N := by simp [a, hc1]
      rw [ha] at htop
      have hle : Submodule.span ℂ (Set.range f) ≤ Subalgebra.toSubmodule S :=
        Submodule.span_le.mpr (by rintro _ ⟨u, rfl⟩; exact hmem u)
      exact hle htop

theorem gelfA_mem_adjoin_qdet : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A), Formalism.REAL.GlRel X →
    ∀ k : ℕ, GlobalTheory.SmoothForms.gelfA X k ∈ Algebra.adjoin ℂ (Set.range (Formalism.REAL.qdet X)) := by
  intro A _ _ n X hX k
  rw [← etr_succ_eq_gelfA]
  exact etr_mem_adjoin_qdet A n X hX (k + 1)

end GlobalTheory.CapelliGelfand
