import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColTorusA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardToMultisetEqDegree

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.ThFr

section Deriv

variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] {F : W → ℂ}

theorem differentiable_polyDeriv (hF : ContDiff ℂ (⊤ : ℕ∞) F) (P : MvPolynomial σ ℂ) (u : σ → W) :
    Differentiable ℂ fun y => polyDeriv P u F y := by
  simp only [polyDeriv_eq_of_subset P u F _ subset_rfl, pdTerm_eq_itD]
  exact Differentiable.fun_sum fun m _ => (itD_differentiable hF _).const_mul _

theorem polyDeriv_mul_X (hF : ContDiff ℂ (⊤ : ℕ∞) F) (P : MvPolynomial σ ℂ) (u : σ → W) (l : σ)
    (x : W) : polyDeriv (P * X l) u F x = fderiv ℂ (fun y => polyDeriv P u F y) x (u l) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial m c =>
    have h (m : σ →₀ ℕ) : (monomial m c : MvPolynomial σ ℂ) = c • monomial m 1 := by
      simp [smul_monomial]
    rw [X, monomial_mul, mul_one, h, h]
    simp only [polyDeriv_smul, polyDeriv_monomial_one, pdTerm_eq_itD]
    rw [fderiv_const_mul (itD_differentiable hF _ x), ContinuousLinearMap.smul_apply, smul_eq_mul,
      ← itD_cons hF, ← List.map_cons]
    refine congrArg _ (congrFun (ct_itD_perm hF (List.Perm.map u ?_)) x)
    rw [← Multiset.coe_eq_coe, ← Multiset.cons_coe, Multiset.coe_toList, Multiset.coe_toList,
      map_add, Finsupp.toMultiset_single, one_nsmul, add_comm, Multiset.singleton_add]
  | add P Q hP hQ =>
    simp only [add_mul, polyDeriv_add, hP, hQ]
    rw [fderiv_fun_add (differentiable_polyDeriv hF P u x) (differentiable_polyDeriv hF Q u x),
      ContinuousLinearMap.add_apply]

theorem polyDeriv_algHom (hF : ContDiff ℂ (⊤ : ℕ∞) F) (Φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ)
    (s : σ → ℂ) (j : σ → σ) (hΦ : ∀ l, Φ (X l) = X l + C (s l) * X (j l)) (u : σ → W)
    (P : MvPolynomial σ ℂ) (x : W) :
    polyDeriv (Φ P) u F x = polyDeriv P (fun l => u l + s l • u (j l)) F x := by
  induction P using MvPolynomial.induction_on generalizing x with
  | C a =>
    have h : (C a : MvPolynomial σ ℂ) = a • monomial 0 1 := by simp [smul_eq_C_mul]
    rw [algHom_C, algebraMap_eq, h]
    simp [polyDeriv_smul, polyDeriv_monomial_one, pdTerm_eq_itD, -smul_monomial, -monomial_zero']
  | add P Q hP hQ => simp only [map_add, polyDeriv_add, hP, hQ]
  | mul_X P l hP =>
    rw [map_mul, hΦ, mul_add, mul_left_comm, C_mul', polyDeriv_add, polyDeriv_smul,
      polyDeriv_mul_X hF, polyDeriv_mul_X hF, polyDeriv_mul_X hF, funext hP]
    simp

end Deriv

section Triangular

variable {J V : Type*} [Fintype J] [DecidableEq J] [AddCommGroup V] [Module ℂ V]

theorem eigen_of_triangular (f : (J → V) → ℂ) (lt : J → J → Prop) (rk : J → ℕ)
    (hrk : ∀ i j, lt i j → rk i < rk j) (d : J → ℕ)
    (hadd : ∀ i j, lt i j → ∀ (s : ℂ) u, f (Function.update u j (u j + s • u i)) = f u)
    (hsc : ∀ j (s : ℂ) u, f (Function.update u j (s • u j)) = s ^ d j * f u)
    (N : J → J → ℂ) (hN : ∀ i j, i ≠ j → ¬ lt i j → N i j = 0) (u : J → V) :
    f (fun j => ∑ i, N i j • u i) = (∏ j, N j j ^ d j) * f u := by
  have hne : ∀ i j, lt i j → i ≠ j := fun i j h e => (hrk i j h).ne (congrArg rk e)
  have one (y : J → V) (j : J) (T : Finset J) (hT : j ∉ T) :
      f (Function.update y j (N j j • y j + ∑ i ∈ T, N i j • y i)) = N j j ^ d j * f y := by
    induction T using Finset.induction_on with
    | empty => simpa using hsc j _ y
    | insert i T hi ih =>
      have hij : i ≠ j := fun e => hT (e ▸ Finset.mem_insert_self _ _)
      rw [Finset.sum_insert hi, ← ih fun h => hT (Finset.mem_insert_of_mem h)]
      by_cases h : lt i j
      · rw [← hadd i j h (N i j) (Function.update y j (N j j • y j + ∑ i ∈ T, N i j • y i)),
          Function.update_idem,
          Function.update_self, Function.update_of_ne hij]
        congr 2
        abel
      · rw [hN i j hij h, zero_smul, zero_add]
  have key (S : Finset J) : f (fun j => if j ∈ S then ∑ i, N i j • u i else u j) =
      (∏ j ∈ S, N j j ^ d j) * f u := by
    induction S using Finset.induction_on_min_value rk with
    | empty => simp
    | insert a S ha hmin ih =>
      rw [Finset.prod_insert ha, mul_assoc, ← ih, ← one _ a (Finset.univ.erase a) (by simp)]
      congr 1
      funext j
      by_cases hj : j = a
      · subst hj
        rw [Function.update_self, if_pos (Finset.mem_insert_self _ _), if_neg ha,
          ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        by_cases h : lt i j
        · rw [if_neg fun hS => (hmin i hS).not_gt (hrk i j h)]
        · rw [hN i j (Finset.ne_of_mem_erase hi) h, zero_smul, zero_smul]
      · simp [Function.update_of_ne hj, hj]
  simpa using key Finset.univ

end Triangular

open Harm in

theorem polyDeriv_triangular {T κ W : Type*} [Fintype T] [Fintype κ] {p q : ℕ}
    [NormedAddCommGroup W] [NormedSpace ℂ W] {F : W → ℂ} (hF : ContDiff ℂ (⊤ : ℕ∞) F)
    {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ} {P : Poly ℂ T p q κ} (hP : P ∈ rowHighest ℂ c c')
    (N : T × (Fin p ⊕ Fin q) → T × (Fin p ⊕ Fin q) → ℂ)
    (hN : ∀ i j, i ≠ j → ¬ (i.1 = j.1 ∧ RowLT i.2 j.2) → N i j = 0) (u : Var T p q κ → W) (x : W) :
    polyDeriv P (fun l => ∑ i, N i (l.1, l.2.1) • u (i.1, i.2, l.2.2)) F x =
      (∏ j, N j j ^ Sum.elim (partOf (c j.1)) (partOf (c' j.1)) j.2) * polyDeriv P u F x := by
  classical
  obtain ⟨-, hdeg, hinv⟩ := mem_rowHighest_iff_rowAdd.1 hP
  have h := eigen_of_triangular
    (fun w : T × (Fin p ⊕ Fin q) → κ → W => polyDeriv P (fun l => w (l.1, l.2.1) l.2.2) F x)
    (fun i j => i.1 = j.1 ∧ RowLT i.2 j.2) (fun i => Sum.elim Fin.val Fin.val i.2) ?_
    (fun j => Sum.elim (partOf (c j.1)) (partOf (c' j.1)) j.2) ?_ ?_ N hN
    fun i k => u (i.1, i.2, k)
  · simpa only [Finset.sum_apply, Pi.smul_apply] using h
  · rintro ⟨t, a | a⟩ ⟨t', b | b⟩ ⟨-, h⟩ <;> first | exact h | exact h.elim
  · rintro ⟨t, r⟩ ⟨t', r'⟩ ⟨rfl, h⟩ s w
    conv_rhs => rw [← rowAdd_eq_self_of_forall_int (hinv t r r' h) s]
    rw [polyDeriv_algHom hF _ (fun l => if l.1 = t ∧ l.2.1 = r' then s else 0)
      (fun l => (t, r, l.2.2)) (fun ⟨t', r'', k⟩ => by rw [rowAdd_X]; split_ifs <;> simp)]
    congr 1
    funext ⟨t', r'', k⟩
    by_cases e : t' = t ∧ r'' = r'
    · obtain ⟨rfl, rfl⟩ := e
      simp
    · rw [Function.update_of_ne (by simpa using e), if_neg e]
      simp
  · rintro ⟨t, r⟩ s w
    rw [← polyDeriv_smul_letter P (fun l => if l.1 = t ∧ l.2.1 = r then s else 1) _ fun m hm => ?_]
    · congr 1
      funext ⟨t', r'', k⟩
      by_cases e : t' = t ∧ r'' = r
      · obtain ⟨rfl, rfl⟩ := e
        simp
      · rw [Function.update_of_ne (by simpa using e), if_neg e]
        simp
    · rw [← hdeg t r (mem_support_iff.1 hm), Finsupp.weight_apply, Finsupp.sum,
        ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [rowInd_apply]
      split_ifs with h <;> simp [h]

end GlobalTheory.ThFr
