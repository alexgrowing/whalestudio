import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.WeightBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Unitary

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem casimir_apply_eq_casimirK_add (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (x : M) :
    casimir E x = casimirK ε E x +
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), E a b (E b a x) := by
  simp only [casimir, casimirK, LinearMap.sum_apply, Module.End.mul_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun b => ε b = ε a)]
  congr 1
  refine Finset.sum_congr (Finset.filter_congr fun b _ => ?_) fun _ _ => rfl
  exact ⟨fun h h' => h h'.symm, fun h h' => h h'.symm⟩

theorem sum_nc_swap (ε : Fin n → Bool) (f : Fin n → Fin n → ℝ) :
    ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), f b a =
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), f a b := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : ε a = ε b
  · simp [h]
  · simp [h, Ne.symm h]

theorem re_inner_casimir_eq (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M}
    (hU : IsInfUnitary ε E) (x : M) :
    RCLike.re (inner ℂ (casimir E x) x) = RCLike.re (inner ℂ (casimirK ε E x) x) -
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 := by
  rw [casimir_apply_eq_casimirK_add ε E x, inner_add_left, map_add, sum_inner, map_sum]
  have key : ∀ a, RCLike.re (inner ℂ (∑ b ∈ univ.filter (fun b => ε a ≠ ε b), E a b (E b a x)) x) =
      -∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E b a x‖ ^ 2 := by
    intro a
    rw [sum_inner, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hab : ε a ≠ ε b := (Finset.mem_filter.1 hb).2
    rw [hU a b (E b a x) x, adjSign, if_neg hab, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  simp only [key, Finset.sum_neg_distrib]
  rw [sum_nc_swap ε (fun a b => ‖E a b x‖ ^ 2)]
  ring

theorem re_inner_smul_self (c : ℝ) (x : M) :
    RCLike.re (inner ℂ ((c : ℂ) • x) x) = c * ‖x‖ ^ 2 := by
  rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

private theorem casimir_eq_smul_on_layer {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) {V : Submodule ℂ M} {c : ℝ} (hc : ∀ v ∈ V, casimir E v = (c : ℂ) • v) :
    ∀ k : ℕ, ∀ x ∈ layer ε E V k, casimir E x = (c : ℂ) • x := by
  intro k
  induction k with
  | zero =>
    intro x hx
    exact hc x hx
  | succ k ih =>
    intro x hx
    have hle : layer ε E V (k + 1) ≤ LinearMap.ker (casimir E - (c : ℂ) • 1) := by
      show layer ε E V k ⊔ _ ≤ _
      refine sup_le (fun y hy => ?_) (iSup_le fun a => iSup_le fun b => iSup_le fun _ => ?_)
      · rw [LinearMap.mem_ker, LinearMap.sub_apply, ih y hy]
        simp
      · rw [Submodule.map_le_iff_le_comap]
        intro y hy
        rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.sub_apply]
        have e := congrArg (fun f => f y) (casimir_comm hE a b)
        simp only [Module.End.mul_apply] at e
        rw [e, ih y hy, map_smul]
        simp
    have h1 := hle hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h1
    simpa using h1

theorem exists_sum_nc_norm_sq_le (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {V : Submodule ℂ M} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V) {c : ℝ}
    (hc : ∀ v ∈ V, casimir E v = (c : ℂ) • v) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ k : ℕ, ∀ x ∈ layer ε E V k,
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 ≤
        ((R + √2 * k) ^ 2 - nsq (rhoC ε) - c) * ‖x‖ ^ 2 := by
  obtain ⟨R, hR, hK⟩ := exists_re_inner_casimirK_layer_le hE hU hVf hVK
  refine ⟨R, hR, fun k x hx => ?_⟩
  have h1 := re_inner_casimir_eq ε hU x
  rw [casimir_eq_smul_on_layer hE hc k x hx, re_inner_smul_self] at h1
  have h2 := hK k x hx
  nlinarith

end Unitary

end ReciprocityTheory.ChartRestriction.DS
