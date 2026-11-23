import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoefficientSpaceEqSpanOrbitExtremalVector
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

namespace GlobalTheory.BrCompare

theorem monomial_eq_zmon_mul_emb {K : Type} [Field K] {n : ℕ} (b : Fin n → ℕ) (μ : Fin (n + 1) × Fin n →₀ ℕ)
    (hμ : ∀ s, μ (Fin.last n, s) = b s) (c : K) :
    ∃ f, (monomial μ c : BP K n) = zmon K n b * emb K n f := by
  refine ⟨C c * ∏ a : Fin n, ∏ s : Fin n, X (a, s) ^ μ (a.castSucc, s), ?_⟩
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, Fin.prod_univ_castSucc]
  simp only [hμ, zmon, emb, map_mul, map_prod, map_pow, rename_X, rename_C]
  ring

theorem eq_zmon_mul_emb_of_homogeneous {K : Type} [Field K] {n : ℕ} (b : Fin n → ℕ) (H : BP K n)
    (hH : IsWeightedHomogeneous (zW n) H (fun s => (b s : ℤ))) : ∃ f, H = zmon K n b * emb K n f := by
  have h : ∀ μ ∈ H.support, ∃ f, (monomial μ (coeff μ H) : BP K n) = zmon K n b * emb K n f := by
    intro μ hμ
    refine monomial_eq_zmon_mul_emb b μ (fun s => ?_) _
    have h1 := congrFun (hH (mem_support_iff.1 hμ)) s
    rw [bm_weight_zW] at h1
    exact_mod_cast h1
  choose! g hg using h
  refine ⟨∑ μ ∈ H.support, g μ, ?_⟩
  rw [map_sum, Finset.mul_sum, ← Finset.sum_congr rfl hg]
  exact H.as_sum

theorem zmon_mul_emb_injective {K : Type} [Field K] {n : ℕ} (b : Fin n → ℕ) {f g : MvPolynomial (Fin n × Fin n) K}
    (h : zmon K n b * emb K n f = zmon K n b * emb K n g) : f = g := by
  have hz : zmon K n b ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => pow_ne_zero _ (X_ne_zero _)
  refine rename_injective (fun v : Fin n × Fin n => ((v.1.castSucc, v.2) : Fin (n + 1) × Fin n)) ?_
    (mul_left_cancel₀ hz h)
  exact (Fin.castSucc_injective n).prodMap Function.injective_id

theorem zcomp_top_eq_zmon_mul_emb (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : Fin n → ℕ) (G : BP K n)
    (hG : G ∈ dualWeyl K (n + 1) n lam) (b : Fin n → ℕ) (hb : ∀ s, b s ≤ lam s)
    (hmax : ∀ β', zcomp K n β' G ≠ 0 → omg β' ≤ omg fun s => (b s : ℤ)) :
    ∃ f ∈ dualWeyl K n n (fun s => lam s - b s), zcomp K n (fun s => (b s : ℤ)) G = zmon K n b * emb K n f := by
  obtain ⟨f, hf⟩ := eq_zmon_mul_emb_of_homogeneous b _ (bmD_zcomp_isWH (fun s => (b s : ℤ)) G)
  refine ⟨f, bm_mem_dualWeyl_iff.2 ⟨fun s => ?_, fun l j hlj => ?_⟩, hf⟩
  · have h := bmD_weight lam G hG (fun s => (b s : ℤ)) s
    rw [hf, bmE_lead, bm_ndE_self] at h
    apply zmon_mul_emb_injective b
    rw [h, map_smul, mul_smul_comm, Nat.cast_sub (hb s)]
    push_cast
    rfl
  · have h := bmD_raise lam G hG (fun s => (b s : ℤ)) hmax l j hlj
    rw [hf, bmE_lead] at h
    apply zmon_mul_emb_injective b
    rw [h, map_zero, mul_zero]

end GlobalTheory.BrCompare
