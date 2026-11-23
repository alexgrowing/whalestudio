import Mathlib

open scoped BigOperators

namespace GlobalTheory.CoordProdDeriv

theorem card_filter_cons {g k : ℕ} (a : Fin g) (σ : Fin k → Fin g) (i : Fin g) :
    (Finset.univ.filter (fun j => (Fin.cons a σ : Fin (k + 1) → Fin g) j = i)).card
      = (Finset.univ.filter (fun j => σ j = i)).card + if a = i then 1 else 0 := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [add_comm]

theorem fderiv_prod_iteratedDeriv {g : ℕ} (f : Fin g → ℂ → ℂ) (hf : ∀ i, Differentiable ℂ (f i))
    (n : Fin g → ℕ) (z : Fin g → ℂ) :
    HasFDerivAt (fun z : Fin g → ℂ => ∏ i, iteratedDeriv (n i) (f i) (z i))
      (∑ a : Fin g, (∏ i, iteratedDeriv (n i + if a = i then 1 else 0) (f i) (z i)) •
        (ContinuousLinearMap.proj a : (Fin g → ℂ) →L[ℂ] ℂ)) z := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin g)),
      HasFDerivAt (fun z : Fin g → ℂ => iteratedDeriv (n i) (f i) (z i))
        (iteratedDeriv (n i + 1) (f i) (z i) •
          (ContinuousLinearMap.proj i : (Fin g → ℂ) →L[ℂ] ℂ)) z := by
    intro i _
    have hd : Differentiable ℂ (iteratedDeriv (n i) (f i)) :=
      ((hf i).contDiff (n := ⊤)).differentiable_iteratedDeriv _ (by
        exact WithTop.coe_lt_top _)
    have h1 : HasDerivAt (iteratedDeriv (n i) (f i)) (iteratedDeriv (n i + 1) (f i) (z i)) (z i) := by
      rw [iteratedDeriv_succ]
      exact (hd (z i)).hasDerivAt
    exact h1.comp_hasFDerivAt z
      (ContinuousLinearMap.proj i : (Fin g → ℂ) →L[ℂ] ℂ).hasFDerivAt
  have h2 := HasFDerivAt.finset_prod h
  refine h2.congr_fderiv (Eq.symm ?_)
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
  congr 2
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [if_neg (Finset.ne_of_mem_erase hi).symm, add_zero]
  · rw [if_pos rfl]

theorem iteratedFDeriv_prod_coord_at {g : ℕ} (f : Fin g → ℂ → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i)) (k : ℕ) :
    ∀ (ys : Fin k → Fin g → ℂ) (z : Fin g → ℂ),
      iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∏ i, f i (z i)) z ys
        = ∑ σ : Fin k → Fin g, (∏ j, ys j (σ j)) *
          ∏ i, iteratedDeriv (Finset.univ.filter (fun j => σ j = i)).card (f i) (z i) := by
  have hF : ContDiff ℂ ⊤ (fun z : Fin g → ℂ => ∏ i, f i (z i)) :=
    contDiff_prod fun i _ => ((hf i).contDiff).comp (contDiff_apply ℂ ℂ i)
  induction k with
  | zero => intro ys z; simp
  | succ k ih =>
    intro ys z
    have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∏ i, f i (z i))) z :=
      hF.differentiable_iteratedFDeriv (m := k) (by exact WithTop.coe_lt_top _) z
    rw [iteratedFDeriv_succ_apply_left, ← fderiv_continuousMultilinear_apply_const_apply hd]
    have e : (fun z => iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∏ i, f i (z i)) z (Fin.tail ys))
        = fun z => ∑ σ : Fin k → Fin g, (∏ j, Fin.tail ys j (σ j)) *
          ∏ i, iteratedDeriv (Finset.univ.filter (fun j => σ j = i)).card (f i) (z i) :=
      funext fun z => ih _ z
    rw [e]
    have h3 := HasFDerivAt.fun_sum (u := Finset.univ) (fun (σ : Fin k → Fin g) _ =>
      (fderiv_prod_iteratedDeriv f hf
        (fun i => (Finset.univ.filter (fun j => σ j = i)).card) z).const_mul
        (∏ j, Fin.tail ys j (σ j)))
    rw [h3.fderiv]
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin g)).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.proj_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun a _ => ?_
    have e2 : (Fin.consEquiv (fun _ : Fin (k + 1) => Fin g)) (a, σ) = Fin.cons a σ := rfl
    simp only [e2, card_filter_cons, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]
    ring

theorem iteratedFDeriv_prod_coord :
    ∀ (g k : ℕ) (f : Fin g → ℂ → ℂ) (ys : Fin k → Fin g → ℂ), (∀ i, Differentiable ℂ (f i)) →
      iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∏ i, f i (z i)) 0 ys
        = ∑ σ : Fin k → Fin g, (∏ j, ys j (σ j)) *
          ∏ i, iteratedDeriv (Finset.univ.filter (fun j => σ j = i)).card (f i) 0 :=
  fun _ k f ys hf => iteratedFDeriv_prod_coord_at f hf k ys 0

end GlobalTheory.CoordProdDeriv
