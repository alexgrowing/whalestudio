import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.LineDerivListEqIteratedFDeriv

open Filter Topology

namespace GlobalTheory

section Def

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

noncomputable def pderivList (l : List ι) (F : (ι → 𝕜) → V) : (ι → 𝕜) → V :=
  lineDerivList 𝕜 (l.map fun k => Pi.single k (1 : 𝕜)) F

noncomputable def pderivIter (α : ι →₀ ℕ) (F : (ι → 𝕜) → V) : (ι → 𝕜) → V :=
  pderivList α.toMultiset.toList F

noncomputable def polyDeriv (P : MvPolynomial ι 𝕜) (F : (ι → 𝕜) → V) (a : ι → 𝕜) : V :=
  ∑ α ∈ P.support, P.coeff α • pderivIter α F a

@[simp] theorem pderivList_nil (F : (ι → 𝕜) → V) : pderivList [] F = F := rfl

theorem pderivList_append (l₁ l₂ : List ι) (F : (ι → 𝕜) → V) :
    pderivList (l₁ ++ l₂) F = pderivList l₁ (pderivList l₂ F) := by
  simp only [pderivList, List.map_append, lineDerivList_append]

@[simp] theorem pderivIter_zero (F : (ι → 𝕜) → V) : pderivIter 0 F = F := by
  simp [pderivIter]

theorem update_eq_add_smul_single (z : ι → 𝕜) (k : ι) (t : 𝕜) :
    Function.update z k t = z + (t - z k) • (Pi.single k 1 : ι → 𝕜) := by
  funext j
  by_cases h : j = k
  · subst h; simp
  · simp [h]

theorem pderivList_replicate (k : ι) (n : ℕ) (F : (ι → 𝕜) → V) (z : ι → 𝕜) :
    pderivList (List.replicate n k) F z
      = iteratedDeriv n (fun t => F (Function.update z k t)) (z k) := by
  have h := lineDerivList_replicate n (Pi.single k (1 : 𝕜) : ι → 𝕜) F z (0 : 𝕜)
  rw [zero_smul, add_zero] at h
  rw [pderivList, List.map_replicate, h]
  simp only [update_eq_add_smul_single]
  rw [iteratedDeriv_comp_sub_const (f := fun s : 𝕜 => F (z + s • (Pi.single k 1 : ι → 𝕜)))]
  simp

theorem pderivIter_single (k : ι) (n : ℕ) (F : (ι → 𝕜) → V) (z : ι → 𝕜) :
    pderivIter (Finsupp.single k n) F z
      = iteratedDeriv n (fun t => F (Function.update z k t)) (z k) := by
  rw [← pderivList_replicate, pderivIter, Finsupp.toMultiset_single]
  congr 1
  rw [← List.perm_replicate, ← Multiset.coe_eq_coe, Multiset.coe_toList,
    Multiset.nsmul_singleton, Multiset.coe_replicate]

@[simp] theorem pderivIter_zero_fun (α : ι →₀ ℕ) :
    pderivIter α (fun _ : ι → 𝕜 => (0 : V)) = fun _ => 0 :=
  lineDerivList_zero _

theorem polyDeriv_eq_sum_of_subset (P : MvPolynomial ι 𝕜) {s : Finset (ι →₀ ℕ)}
    (hs : P.support ⊆ s) (F : (ι → 𝕜) → V) (a : ι → 𝕜) :
    polyDeriv P F a = ∑ α ∈ s, P.coeff α • pderivIter α F a := by
  refine Finset.sum_subset hs fun α _ hα => ?_
  rw [MvPolynomial.notMem_support_iff.1 hα, zero_smul]

noncomputable def polyDerivLinear (F : (ι → 𝕜) → V) (a : ι → 𝕜) : MvPolynomial ι 𝕜 →ₗ[𝕜] V where
  toFun P := polyDeriv P F a
  map_add' P Q := by
    classical
    rw [polyDeriv_eq_sum_of_subset (P + Q) (s := P.support ∪ Q.support) MvPolynomial.support_add,
      polyDeriv_eq_sum_of_subset P (s := P.support ∪ Q.support) Finset.subset_union_left,
      polyDeriv_eq_sum_of_subset Q (s := P.support ∪ Q.support) Finset.subset_union_right,
      ← Finset.sum_add_distrib]
    simp only [MvPolynomial.coeff_add, add_smul]
  map_smul' c P := by
    rw [polyDeriv_eq_sum_of_subset (c • P) (s := P.support) MvPolynomial.support_smul,
      polyDeriv, Finset.smul_sum]
    simp only [MvPolynomial.coeff_smul, smul_eq_mul, mul_smul, RingHom.id_apply]

@[simp] theorem polyDerivLinear_apply (F : (ι → 𝕜) → V) (a : ι → 𝕜) (P : MvPolynomial ι 𝕜) :
    polyDerivLinear F a P = polyDeriv P F a := rfl

@[simp] theorem polyDeriv_zero (F : (ι → 𝕜) → V) (a : ι → 𝕜) :
    polyDeriv (0 : MvPolynomial ι 𝕜) F a = 0 := (polyDerivLinear F a).map_zero

@[simp] theorem polyDeriv_monomial (α : ι →₀ ℕ) (c : 𝕜) (F : (ι → 𝕜) → V) (a : ι → 𝕜) :
    polyDeriv (MvPolynomial.monomial α c) F a = c • pderivIter α F a := by
  rw [polyDeriv_eq_sum_of_subset _ (s := {α}) MvPolynomial.support_monomial_subset]
  simp

@[simp] theorem polyDeriv_C (c : 𝕜) (F : (ι → 𝕜) → V) (a : ι → 𝕜) :
    polyDeriv (MvPolynomial.C c) F a = c • F a := by
  rw [← MvPolynomial.monomial_zero', polyDeriv_monomial, pderivIter_zero]

@[simp] theorem polyDeriv_one (F : (ι → 𝕜) → V) (a : ι → 𝕜) :
    polyDeriv (1 : MvPolynomial ι 𝕜) F a = F a := by
  rw [← MvPolynomial.C_1, polyDeriv_C, one_smul]

@[simp] theorem polyDeriv_zero_fun (P : MvPolynomial ι 𝕜) (a : ι → 𝕜) :
    polyDeriv P (fun _ => (0 : V)) a = 0 := by
  simp [polyDeriv]

end Def

section Analytic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι] [Fintype ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

variable [CompleteSpace V]

theorem analyticAt_pderivIter {F : (ι → 𝕜) → V} {a : ι → 𝕜} (h : AnalyticAt 𝕜 F a)
    (α : ι →₀ ℕ) : AnalyticAt 𝕜 (pderivIter α F) a :=
  analyticAt_lineDerivList h _

theorem pderivList_perm {F : (ι → 𝕜) → V} {a : ι → 𝕜} (h : AnalyticAt 𝕜 F a) {l₁ l₂ : List ι}
    (hl : l₁.Perm l₂) : pderivList l₁ F a = pderivList l₂ F a :=
  lineDerivList_perm h (hl.map _)

theorem pderivIter_add_index {F : (ι → 𝕜) → V} {a : ι → 𝕜} (h : AnalyticAt 𝕜 F a)
    (α β : ι →₀ ℕ) : pderivIter (α + β) F a = pderivIter α (pderivIter β F) a := by
  rw [pderivIter, pderivIter, pderivIter, ← pderivList_append]
  refine pderivList_perm h ?_
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_add]
  simp only [Multiset.coe_toList, map_add]

end Analytic

section Polynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι]

theorem hasDerivAt_eval_line (Q : MvPolynomial ι 𝕜) (z : ι → 𝕜) (k : ι) :
    HasDerivAt (fun t : 𝕜 => MvPolynomial.eval (z + t • (Pi.single k 1 : ι → 𝕜)) Q)
      (MvPolynomial.eval z (MvPolynomial.pderiv k Q)) 0 := by
  induction Q using MvPolynomial.induction_on with
  | C c => simpa using hasDerivAt_const (0 : 𝕜) c
  | add P Q hP hQ => simpa using hP.fun_add hQ
  | mul_X P j hP =>
    have hj : HasDerivAt (fun t : 𝕜 => z j + t * (Pi.single k 1 : ι → 𝕜) j)
        ((Pi.single k 1 : ι → 𝕜) j) 0 := by
      simpa using ((hasDerivAt_id (0 : 𝕜)).mul_const ((Pi.single k 1 : ι → 𝕜) j)).const_add (z j)
    have := hP.fun_mul hj
    have e : (fun t : 𝕜 => MvPolynomial.eval (z + t • (Pi.single k 1 : ι → 𝕜))
        (P * MvPolynomial.X j)) = fun t : 𝕜 =>
          MvPolynomial.eval (z + t • (Pi.single k 1 : ι → 𝕜)) P
            * (z j + t * (Pi.single k 1 : ι → 𝕜) j) := by
      funext t; simp
    rw [e]
    refine this.congr_deriv ?_
    by_cases h : j = k
    · subst h; simp [add_comm, mul_comm]
    · simp [h, mul_comm]

end Polynomial

section Cauchy

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

private theorem cauchy_estimate_iterated_pderiv {F : (ι → ℂ) → V} {a : ι → ℂ} {r : ι → ℝ} {M : ℝ} (α : ι →₀ ℕ)
    (hr : ∀ k, 0 ≤ r k) (hα : ∀ k, α k ≠ 0 → 0 < r k)
    (hF : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ ≤ r k) → AnalyticAt ℂ F z)
    (hM : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ = r k) → ‖F z‖ ≤ M) (s : Finset ι) :
    ∀ z : ι → ℂ, (∀ k ∈ s, z k = a k) → (∀ k ∉ s, ‖z k - a k‖ = r k) →
      ‖pderivIter (∑ k ∈ s, Finsupp.single k (α k)) F z‖
        ≤ (∏ k ∈ s, ((α k).factorial : ℝ)) * M / ∏ k ∈ s, r k ^ α k := by
  induction s using Finset.induction_on with
  | empty => intro z _ hz; simpa using hM z fun k => hz k (by simp)
  | insert j s hj ih =>
    intro z hz hz'
    have hzj : z j = a j := hz j (Finset.mem_insert_self _ _)
    have hup : ∀ t : ℂ, ‖t - a j‖ ≤ r j → AnalyticAt ℂ F (Function.update z j t) := by
      intro t ht
      refine hF _ fun k => ?_
      by_cases hk : k = j
      · subst hk; simpa using ht
      · rw [Function.update_of_ne hk]
        by_cases hks : k ∈ s
        · simpa [hz k (Finset.mem_insert_of_mem hks)] using hr k
        · exact (hz' k (by simp [hk, hks])).le
    have hb : ∀ t : ℂ, ‖t - a j‖ = r j →
        ‖pderivIter (∑ k ∈ s, Finsupp.single k (α k)) F (Function.update z j t)‖
          ≤ (∏ k ∈ s, ((α k).factorial : ℝ)) * M / ∏ k ∈ s, r k ^ α k := by
      intro t ht
      refine ih _ (fun k hk => ?_) (fun k hk => ?_)
      · rw [Function.update_of_ne (ne_of_mem_of_not_mem hk hj)]
        exact hz k (Finset.mem_insert_of_mem hk)
      · by_cases hkj : k = j
        · subst hkj; simpa using ht
        · rw [Function.update_of_ne hkj]
          exact hz' k (by simp [hkj, hk])
    have hza : AnalyticAt ℂ F z := by
      have := hup (z j) (by simpa [hzj] using hr j)
      rwa [Function.update_eq_self] at this
    rw [Finset.sum_insert hj, pderivIter_add_index hza, pderivIter_single, Finset.prod_insert hj,
      Finset.prod_insert hj, hzj]
    rcases (hr j).eq_or_lt with h0 | hpos
    · have hαj : α j = 0 := by
        by_contra hne
        exact (hα j hne).ne h0
      simpa [hαj] using hb (a j) (by simpa using h0)
    · have hd : DiffContOnCl ℂ (fun t => pderivIter (∑ k ∈ s, Finsupp.single k (α k)) F
          (Function.update z j t)) (Metric.ball (a j) (r j)) := by
        refine DifferentiableOn.diffContOnCl fun t ht => ?_
        rw [closure_ball _ hpos.ne', mem_closedBall_iff_norm] at ht
        exact ((analyticAt_pderivIter (hup t ht) _).differentiableAt.comp t
          (hasDerivAt_update z j t).differentiableAt).differentiableWithinAt
      refine (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (α j) hpos hd
        fun t ht => hb t (mem_sphere_iff_norm.1 ht)).trans_eq ?_
      ring

theorem norm_pderivIter_le_of_analyticAt {F : (ι → ℂ) → V} {a : ι → ℂ} {r : ι → ℝ} {M : ℝ}
    (α : ι →₀ ℕ) (hr : ∀ k, 0 ≤ r k) (hα : ∀ k, α k ≠ 0 → 0 < r k)
    (hF : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ ≤ r k) → AnalyticAt ℂ F z)
    (hM : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ = r k) → ‖F z‖ ≤ M) :
    ‖pderivIter α F a‖ ≤ (∏ k, ((α k).factorial : ℝ)) * M / ∏ k, r k ^ α k := by
  have h := cauchy_estimate_iterated_pderiv α hr hα hF hM Finset.univ a (fun _ _ => rfl) (by simp)
  rwa [Finsupp.univ_sum_single] at h

end Cauchy

end GlobalTheory
