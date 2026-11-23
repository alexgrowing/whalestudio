import Mathlib

open Set Metric Filter Topology
open scoped Nat

namespace GlobalTheory

section Periodic

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem entire_apply_eq_of_values_on_compact {F : E → V} (hF : Differentiable ℂ F) {K : Set E}
    (hK : IsCompact K) (hcov : ∀ x, ∃ k ∈ K, F x = F k) (z w : E) : F z = F w := by
  refine hF.apply_eq_apply_of_bounded ((hK.image hF.continuous).isBounded.subset ?_) z w
  rintro _ ⟨x, rfl⟩
  obtain ⟨k, hk, h⟩ := hcov x
  exact ⟨k, hk, h.symm⟩

theorem entire_apply_eq_of_periodic_of_compact {F : E → V} (hF : Differentiable ℂ F)
    {G K : Set E} (hK : IsCompact K) (hcov : ∀ x, ∃ k ∈ K, ∃ g ∈ G, x = k + g)
    (hper : ∀ x, ∀ g ∈ G, F (x + g) = F x) (z w : E) : F z = F w := by
  refine entire_apply_eq_of_values_on_compact hF hK (fun x => ?_) z w
  obtain ⟨k, hk, g, hg, rfl⟩ := hcov x
  exact ⟨k, hk, hper k g hg⟩

theorem entire_apply_eq_of_periodic_of_bounded [FiniteDimensional ℂ E] {F : E → V}
    (hF : Differentiable ℂ F) {G K : Set E} (hK : Bornology.IsBounded K)
    (hcov : ∀ x, ∃ k ∈ K, ∃ g ∈ G, x = k + g)
    (hper : ∀ x, ∀ g ∈ G, F (x + g) = F x) (z w : E) : F z = F w := by
  haveI : ProperSpace E := FiniteDimensional.proper ℂ E
  refine entire_apply_eq_of_periodic_of_compact hF hK.isCompact_closure (fun x => ?_) hper z w
  obtain ⟨k, hk, g, hg, h⟩ := hcov x
  exact ⟨k, subset_closure hk, g, hg, h⟩

theorem entire_const_of_addSubgroup_periodic [FiniteDimensional ℂ E] {F : E → V}
    (hF : Differentiable ℂ F) (G : AddSubgroup E) {K : Set E} (hK : Bornology.IsBounded K)
    (hcov : ∀ x, ∃ g ∈ G, ∃ k ∈ K, x = g + k)
    (hper : ∀ x, ∀ g ∈ G, F (x + g) = F x) : ∃ c, ∀ z, F z = c := by
  refine ⟨F 0, fun z => entire_apply_eq_of_periodic_of_bounded hF (G := G) hK (fun x => ?_)
    hper z 0⟩
  obtain ⟨g, hg, k, hk, h⟩ := hcov x
  exact ⟨k, hk, g, hg, h.trans (add_comm _ _)⟩

theorem entire_apply_eq_of_isZLattice_periodic [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : E → V} (hF : Differentiable ℂ F) (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (hper : ∀ x, ∀ g ∈ L, F (x + g) = F x) (z w : E) : F z = F w :=
  hF.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L F hF.continuous hper).isBounded z w

omit [NormedSpace ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V] in

theorem periodic_of_mem_span_int {F : E → V} {S : Set E}
    (hper : ∀ x, ∀ g ∈ S, F (x + g) = F x) :
    ∀ x, ∀ g ∈ Submodule.span ℤ S, F (x + g) = F x := by
  let P : AddSubgroup E :=
    { carrier := {g | ∀ x, F (x + g) = F x}
      zero_mem' := fun x => by simp
      add_mem' := fun {a b} ha hb x => by rw [← add_assoc, hb, ha]
      neg_mem' := fun {a} ha x => by rw [← ha (x + -a)]; simp }
  intro x g hg
  have : Submodule.span ℤ S ≤ AddSubgroup.toIntSubmodule P :=
    Submodule.span_le.2 fun s hs y => hper y s hs
  exact this hg x

theorem entire_apply_eq_of_periodic_of_span_real [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : E → V} (hF : Differentiable ℂ F) {S : Set E} (hS : Submodule.span ℝ S = ⊤)
    (hper : ∀ x, ∀ g ∈ S, F (x + g) = F x) (z w : E) : F z = F w := by
  obtain ⟨t, htS, hspan, hli⟩ := exists_linearIndependent ℝ S
  let b : Module.Basis t ℝ E := Module.Basis.mk hli (by simp [hspan, hS])
  haveI : Finite t := Module.Finite.finite_basis b
  refine entire_apply_eq_of_isZLattice_periodic hF (Submodule.span ℤ (range b))
    (periodic_of_mem_span_int ?_) z w
  rintro x _ ⟨i, rfl⟩
  exact hper x _ (by simpa [b] using htS i.2)

end Periodic

section Polynomial

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem iteratedDeriv_zero_eq_zero_of_poly_bound {F : ℂ → V} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) {n : ℕ} (hn : m < n) :
    iteratedDeriv n F 0 = 0 := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (hb 0)
  have key : ∀ R : ℝ, 1 ≤ R → ‖iteratedDeriv n F 0‖ ≤ (n ! * C * 2 ^ m) / R := by
    intro R hR
    have hR0 : 0 < R := by linarith
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0) (R := R)
      (C := C * (2 ^ m * R ^ m)) n hR0 hF.diffContOnCl (fun z hz => by
        have hz' : ‖z‖ = R := by simpa using hz
        refine (hb z).trans ?_
        rw [hz', ← mul_pow]
        gcongr
        linarith)
    refine h.trans ?_
    rw [div_le_div_iff₀ (by positivity) hR0]
    have : R ^ m * R ≤ R ^ n := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ hR hn
    calc (n ! : ℝ) * (C * (2 ^ m * R ^ m)) * R = (n ! * C * 2 ^ m) * (R ^ m * R) := by ring
      _ ≤ _ := by gcongr
  have lim : Tendsto (fun R : ℝ => (n ! * C * 2 ^ m) / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  exact norm_le_zero_iff.1 (ge_of_tendsto lim ((eventually_ge_atTop 1).mono key))

theorem entire_eq_taylor_sum_of_poly_bound {F : ℂ → V} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) (z : ℂ) :
    F z = ∑ k ∈ Finset.range (m + 1), z ^ k • ((k ! : ℂ)⁻¹ • iteratedDeriv k F 0) := by
  have h := Complex.hasSum_taylorSeries_of_entire hF 0 z
  have h2 := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (f := fun n : ℕ => (n ! : ℂ)⁻¹ • (z - 0) ^ n • iteratedDeriv n F 0)
    (s := Finset.range (m + 1)) (fun n hn => by
      have : m < n := by simpa using hn
      simp [iteratedDeriv_zero_eq_zero_of_poly_bound hF hb this])
  rw [h.unique h2]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sub_zero, smul_comm]

theorem entire_exists_coeff_of_poly_bound {F : ℂ → V} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃ a : ℕ → V, ∀ z, F z = ∑ k ∈ Finset.range (m + 1), z ^ k • a k :=
  ⟨_, entire_eq_taylor_sum_of_poly_bound hF hb⟩

theorem entire_exists_polynomial_of_poly_bound {F : ℂ → ℂ} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ m ∧ ∀ z, F z = p.eval z := by
  obtain ⟨a, ha⟩ := entire_exists_coeff_of_poly_bound hF hb
  refine ⟨∑ k ∈ Finset.range (m + 1), Polynomial.monomial k (a k), ?_, fun z => ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    exact (Polynomial.natDegree_monomial_le _).trans (by simpa [Nat.lt_succ_iff] using hk)
  · rw [ha z, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [mul_comm]

end Polynomial

end GlobalTheory
