import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMemOfQdetMem
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasimirScalarOfCapelliDeterminantEigenvalue
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CasCentre

open Finset Polynomial

variable {A : Type} [Ring A] [Algebra ℂ A]

def pS {n : ℕ} (s : Finset (Fin n)) : ℂ[X] := ∏ l ∈ s, (X - C ((l : ℕ) : ℂ))

theorem natDegree_pS {n : ℕ} (s : Finset (Fin n)) : (pS s).natDegree = s.card :=
  natDegree_finsetProd_X_sub_C_eq_card _ _

theorem prod_eq_sum {n : ℕ} (s : Finset (Fin n)) (u : ℂ) :
    ∏ l ∈ s, (u - (l : ℂ)) = ∑ k ∈ range (n + 1), u ^ k * (pS s).coeff k := by
  have h1 : (pS s).eval u = ∏ l ∈ s, (u - (l : ℂ)) := by simp [pS, eval_prod]
  have h2 : (pS s).natDegree < n + 1 := by
    rw [natDegree_pS]; have := Finset.card_le_univ s; simp at this; omega
  rw [← h1, eval_eq_sum_range' h2]
  exact sum_congr rfl fun k _ => mul_comm _ _

theorem coeff_pS_top {n : ℕ} (s : Finset (Fin n)) : (pS s).coeff s.card = 1 := by
  have hm : (pS s).Monic := monic_prod_of_monic _ _ fun l _ => monic_X_sub_C _
  rw [← natDegree_pS]; exact hm.coeff_natDegree

theorem coeff_pS_next {n : ℕ} (s : Finset (Fin n)) (hs : 0 < s.card) :
    (pS s).coeff (s.card - 1) = -∑ l ∈ s, (l : ℂ) := by
  have h := prod_X_sub_C_nextCoeff (s := s) (fun l : Fin n => ((l : ℕ) : ℂ))
  rw [nextCoeff_of_natDegree_pos (by rw [natDegree_finsetProd_X_sub_C_eq_card]; exact hs),
    natDegree_finsetProd_X_sub_C_eq_card] at h
  exact h

theorem sum_fin_cast (n : ℕ) : 2 * ∑ l : Fin n, (l : ℂ) = (n : ℂ) * ((n : ℂ) - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h := Finset.sum_range_id_mul_two n
  rw [Fin.sum_univ_eq_sum_range (fun l => ((l : ℕ) : ℂ)) n]
  have h' : ((∑ i ∈ range n, i : ℕ) : ℂ) * 2 = ((n * (n - 1) : ℕ) : ℂ) := by exact_mod_cast h
  rw [Nat.cast_mul, Nat.cast_sub (by omega)] at h'
  push_cast at h'
  linear_combination h'

theorem cas_mem_of_qdet_mem {n : ℕ} (X : Fin n → Fin n → A) (hX : Formalism.REAL.GlRel X) (S : Subalgebra ℂ A)
    (h : ∀ u : ℂ, Formalism.REAL.qdet X u ∈ S) : Formalism.REAL.Cas X ∈ S := by
  classical
  have hT : ∑ i, X i i ∈ S := GlobalTheory.CapTrace.trace_mem_of_qdet_mem X S h
  rcases lt_or_ge n 2 with hn | hn
  · have e : Formalism.REAL.Cas X = (∑ i, X i i) * (∑ i, X i i) := by
      interval_cases n <;> simp [Formalism.REAL.Cas]
    rw [e]; exact S.mul_mem hT hT
  obtain ⟨Rm, hR⟩ := GlobalTheory.qdet_top_three_orders A n X
  let Cf : ℕ → A := fun k => (pS (univ : Finset (Fin n))).coeff k • (1 : A) +
    ∑ i, (pS (univ.erase i)).coeff k • X i i +
    ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (pS ((univ.erase i).erase j)).coeff k • (X i i * X j j - X j i * X i j) +
    (if k < n - 2 then Rm k else 0)
  have hexp : ∀ u : ℂ, Formalism.REAL.qdet X u = ∑ k ∈ range (n + 1), u ^ k • Cf k := by
    intro u
    have hRm : ∑ k ∈ range (n + 1), u ^ k • (if k < n - 2 then Rm k else 0) = ∑ d ∈ range (n - 2), u ^ d • Rm d := by
      simp only [smul_ite, smul_zero]
      rw [← Finset.sum_filter]
      congr 1
      ext k; simp only [mem_filter, mem_range]; omega
    rw [hR u]
    simp only [Cf, smul_add, sum_add_distrib, hRm, prod_eq_sum, sum_smul, smul_sum, smul_smul]
    congr 1
    congr 1
    · congr 1
      exact sum_comm
    · rw [sum_comm]
      refine sum_congr rfl fun i _ => ?_
      exact sum_comm
  have hmem : Cf (n - 2) ∈ S :=
    GlobalTheory.CapTrace.coeff_mem (Subalgebra.toSubmodule S) n Cf (fun u => by rw [← hexp]; exact h u) (n - 2) (by omega)
  have hc2 : ∀ i : Fin n, ∀ j ∈ univ.filter (fun j => i < j), (pS ((univ.erase i).erase j)).coeff (n - 2) = 1 := by
    intro i j hj
    have hij : j ≠ i := (mem_filter.1 hj).2.ne'
    have hc : ((univ.erase i).erase j).card = n - 2 := by
      rw [card_erase_of_mem (mem_erase.2 ⟨hij, mem_univ _⟩), card_erase_of_mem (mem_univ _), card_univ,
        Fintype.card_fin]; omega
    rw [← hc]; exact coeff_pS_top _
  have hc1 : ∀ i : Fin n, (pS (univ.erase i)).coeff (n - 2) = -∑ l ∈ univ.erase i, (l : ℂ) := by
    intro i
    have hc : (univ.erase i).card = n - 1 := by rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    have := coeff_pS_next (univ.erase i) (by omega)
    rw [hc, show n - 1 - 1 = n - 2 by omega] at this
    exact this
  set c := (pS (univ : Finset (Fin n))).coeff (n - 2)
  have hC : Cf (n - 2) = c • (1 : A) + ∑ i, (pS (univ.erase i)).coeff (n - 2) • X i i +
      ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (X i i * X j j - X j i * X i j) := by
    simp only [Cf, lt_irrefl, if_false, add_zero]
    congr 1
    exact sum_congr rfl fun i _ => sum_congr rfl fun j hj => by rw [hc2 i j hj, one_smul]
  have h3 : ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • X i i + (2 : ℂ) • ∑ i, (pS (univ.erase i)).coeff (n - 2) • X i i
      = -(((n : ℂ) - 1) ^ 2) • ∑ i, X i i := by
    rw [smul_sum, smul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [smul_smul, ← add_smul, hc1, sum_erase_eq_sub (mem_univ _)]
    congr 1
    have := sum_fin_cast n
    linear_combination (-1 : ℂ) * this
  have h1 := GlobalTheory.CapelliCasimir.sq_sub_cas X hX
  have key : Formalism.REAL.Cas X = (∑ i, X i i) * (∑ i, X i i) - (2 : ℂ) • Cf (n - 2) + (2 * c) • (1 : A)
      - (((n : ℂ) - 1) ^ 2) • ∑ i, X i i := by
    linear_combination (norm := module) (-1 : ℂ) • h1 + (2 : ℂ) • hC + h3
  rw [key]
  exact S.sub_mem (S.add_mem (S.sub_mem (S.mul_mem hT hT) (S.smul_mem hmem _)) (S.smul_mem (S.one_mem) _))
    (S.smul_mem hT _)

theorem cas_Eop_mem_Zalg : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (τ : E →+* ℂ),
    Formalism.REAL.Cas (Eop (a := a) τ) ∈ Zalg E a := by
  intro E _ _ _ a τ
  refine cas_mem_of_qdet_mem (Eop τ) (glRel_Eop τ) (Zalg E a) fun u => ?_
  have e : Formalism.REAL.qdet (Eop (a := a) τ) u = cap τ (u - ((a : ℂ) - 1) / 2) := by
    rw [cap]; congr 1; ring
  rw [e]
  exact Algebra.subset_adjoin ⟨τ, _, rfl⟩

end GlobalTheory.CasCentre
