import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec

open UpperTheory.ConvolutionTheory.Ci

namespace UpperTheory.ConvolutionTheory.Ci.ExponentialForm

open Polynomial

private theorem semiconj_aeval {A : Type} [Ring A] [Algebra ℂ A] {a x y : A} (h : SemiconjBy a x y) (p : ℂ[X]) :
    SemiconjBy a (aeval x p) (aeval y p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using hp.add_right hq
  | monomial n c =>
    simp only [aeval_monomial, ← Algebra.smul_def]
    have := (h.pow_right n).eq
    unfold SemiconjBy
    rw [mul_smul_comm, smul_mul_assoc, this]

private theorem nil_mul {A : Type} [Ring A] (l : ℕ) (hl : 0 < l) (M : ZMod l → A) (B : A)
    (hc : ∀ i k, Commute (M i) (M k)) (hB : ∀ i, B * M i = M (i + 1) * B) (h0 : IsNilpotent (M 0)) :
    IsNilpotent (M 0 * B) := by
  have h1 : ∀ (m : ℕ) (i : ZMod l), B ^ m * M i = M (i + m) * B ^ m := by
    intro m
    induction m with
    | zero => intro i; simp
    | succ m ih =>
      intro i
      rw [pow_succ', mul_assoc, ih, ← mul_assoc, hB, mul_assoc, Nat.cast_succ, add_assoc]
  have h2 : ∀ m : ℕ, ∃ P : A, Commute (M 0) P ∧ (M 0 * B) ^ (m + 1) = M 0 * (P * B ^ (m + 1)) := by
    intro m
    induction m with
    | zero => exact ⟨1, Commute.one_right _, by simp⟩
    | succ m ih =>
      obtain ⟨P, hP, h⟩ := ih
      refine ⟨P * M (0 + ((m + 1 : ℕ) : ZMod l)), hP.mul_right (hc _ _), ?_⟩
      rw [pow_succ, h, pow_succ B (m + 1)]
      simp only [mul_assoc]
      rw [← mul_assoc (B ^ (m + 1)) (M 0), h1, mul_assoc]
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  obtain ⟨P, hP, h⟩ := h2 m
  have h3 : Commute (M 0) (B ^ (m + 1)) := by
    have := h1 (m + 1) 0
    rw [ZMod.natCast_self, add_zero] at this
    exact this.symm
  have h4 : IsNilpotent ((M 0 * B) ^ (m + 1)) := by
    rw [h]
    exact (hP.mul_right h3).isNilpotent_mul_right h0
  exact h4.of_pow

private theorem nil_nodal {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (U : Module.End ℂ W) :
    IsNilpotent (aeval U (Lagrange.nodal U.charpoly.roots.toFinset id)) := by
  classical
  set r := Lagrange.nodal U.charpoly.roots.toFinset id with hr
  have h1 : U.charpoly = (U.charpoly.roots.map fun a => X - C a).prod :=
    (IsAlgClosed.splits U.charpoly).eq_prod_roots_of_monic U.charpoly_monic
  have h2 : (U.charpoly.roots.map fun a => X - C a).prod ∣ (U.charpoly.roots.map fun _ => r).prod :=
    Multiset.prod_dvd_prod_of_dvd _ _ fun a ha =>
      Lagrange.X_sub_C_dvd_nodal id (Multiset.mem_toFinset.2 ha)
  rw [← h1, Multiset.map_const', Multiset.prod_replicate] at h2
  obtain ⟨q, hq⟩ := h2
  refine ⟨U.charpoly.roots.card, ?_⟩
  rw [← map_pow, hq, map_mul, LinearMap.aeval_self_charpoly, zero_mul]

private theorem pow_eq (s : Finset ℂ) (j : ℕ) :
    ∃ q : ℂ[X], X ^ j = Lagrange.nodal s id * q + ∑ z ∈ s, C (z ^ j) * Lagrange.basis s id z := by
  classical
  have h : Lagrange.nodal s id ∣ X ^ j - ∑ z ∈ s, C (z ^ j) * Lagrange.basis s id z := by
    unfold Lagrange.nodal
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro a _ b _ hab
      exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 hab).isUnit
    · intro a ha
      rw [dvd_iff_isRoot, IsRoot.def, eval_sub]
      have := Lagrange.eval_interpolate_at_node (s := s) (v := id) (fun z : ℂ => z ^ j) (Set.injOn_id _) ha
      rw [Lagrange.interpolate_apply] at this
      rw [this]
      simp
  obtain ⟨q, hq⟩ := h
  exact ⟨q, by rw [← hq]; ring⟩

private theorem trace_eq {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (l : ℕ) (hl : 0 < l)
    (U : ZMod l → Module.End ℂ W) (B : Module.End ℂ W) (hc : ∀ i k, Commute (U i) (U k))
    (hB : ∀ i, B * U i = U (i + 1) * B) :
    ∃ (s : Finset ℂ) (p : ℂ → ℂ[X]), ∀ j : ℕ, LinearMap.trace ℂ W (U 0 ^ j * B) =
      ∑ z ∈ s, LinearMap.trace ℂ W (aeval (U 0) (p z) * B) * z ^ j := by
  classical
  refine ⟨(U 0).charpoly.roots.toFinset, Lagrange.basis (U 0).charpoly.roots.toFinset id, fun j => ?_⟩
  obtain ⟨q, hq⟩ := pow_eq (U 0).charpoly.roots.toFinset j
  have hn := nil_nodal (U 0)
  set r := Lagrange.nodal (U 0).charpoly.roots.toFinset id with hr
  have h1 : IsNilpotent (aeval (U 0) (r * q) * B) := by
    refine nil_mul l hl (fun i => aeval (U i) (r * q)) B (fun i k => ?_) (fun i => semiconj_aeval (hB i) _) ?_
    · exact Commute.symm (semiconj_aeval (Commute.symm (semiconj_aeval (hc i k) _)) _)
    · have : Commute (aeval (U 0) r) (aeval (U 0) q) := (Commute.all r q).map _
      simp only [map_mul]
      exact this.isNilpotent_mul_right hn
  have h2 : LinearMap.trace ℂ W (aeval (U 0) (r * q) * B) = 0 :=
    (LinearMap.isNilpotent_trace_of_isNilpotent h1).eq_zero
  have h3 : U 0 ^ j = aeval (U 0) (X ^ j : ℂ[X]) := by simp
  rw [h3, hq, map_add, add_mul, map_add, h2, zero_add, map_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [map_mul (aeval (U 0)), aeval_C, ← Algebra.smul_def, smul_mul_assoc, map_smul, smul_eq_mul, mul_comm]

end UpperTheory.ConvolutionTheory.Ci.ExponentialForm

theorem UpperTheory.ConvolutionTheory.Ci.expForm :
    ExpForm := by
  classical
  intro W _ _ _ l hl U B hc hB
  obtain ⟨s, p, h⟩ := ExponentialForm.trace_eq l hl U B hc hB
  refine ⟨s.erase 0, fun z => LinearMap.trace ℂ W (Polynomial.aeval (U 0) (p z) * B), Finset.notMem_erase _ _,
    fun j hj => ?_⟩
  rw [h j]
  refine (Finset.sum_erase _ ?_).symm
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have : Subsingleton W := Module.finrank_zero_iff.1 (Nat.le_zero.1 hj)
    rw [Subsingleton.elim (Polynomial.aeval (U 0) (p 0) * B) 0, map_zero, zero_mul]
  · rw [zero_pow hj0.ne', mul_zero]
