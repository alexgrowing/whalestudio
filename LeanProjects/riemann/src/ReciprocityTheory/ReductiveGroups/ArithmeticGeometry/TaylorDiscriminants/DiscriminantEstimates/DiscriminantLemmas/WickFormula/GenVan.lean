import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.WickFormula.GenDefs

open MvPolynomial

namespace PI.WickFormula.Gen

section
variable {K σ ι : Type} [CommRing K] [Fintype ι]

noncomputable def lowDeg (f : ι → σ) (t : ℕ) : Submodule K (MvPolynomial σ K) :=
  restrictSupport K {m | ∑ i, m (f i) < t}

theorem mem_lowDeg {f : ι → σ} {t : ℕ} {R : MvPolynomial σ K} :
    R ∈ lowDeg f t ↔ ∀ m ∈ R.support, ∑ i, m (f i) < t := by
  unfold lowDeg
  rw [mem_restrictSupport_iff]
  exact Iff.rfl

theorem eq_zero_of_mem_lowDeg_zero {f : ι → σ} {R : MvPolynomial σ K}
    (h : R ∈ lowDeg f 0) : R = 0 := by
  rw [mem_lowDeg] at h
  ext m
  rw [coeff_zero]
  by_contra hne
  exact Nat.not_lt_zero _ (h m (mem_support_iff.mpr hne))

private lemma monomial_mem_lowDeg_of_weighted_sum_lt {f : ι → σ} {t : ℕ} {m : σ →₀ ℕ} (c : K)
    (h : ∑ i, m (f i) < t) : monomial m c ∈ lowDeg f t := by
  rw [mem_lowDeg]
  intro m' hm'
  rw [Finset.mem_singleton.mp (support_monomial_subset hm')]
  exact h

theorem pderiv_mem_lowDeg {f : ι → σ} {t : ℕ} (k : σ) {R : MvPolynomial σ K}
    (h : R ∈ lowDeg f t) : pderiv k R ∈ lowDeg f t := by
  have hR := mem_lowDeg.mp h
  rw [R.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [pderiv_monomial]
  apply monomial_mem_lowDeg_of_weighted_sum_lt
  exact lt_of_le_of_lt (Finset.sum_le_sum fun i _ => (Finsupp.tsub_apply _ _ _).trans_le (Nat.sub_le _ _)) (hR m hm)

theorem pderiv_mem_lowDeg_of_succ {f : ι → σ} {t : ℕ} (i : ι) {R : MvPolynomial σ K}
    (h : R ∈ lowDeg f (t + 1)) : pderiv (f i) R ∈ lowDeg f t := by
  classical
  have hR := mem_lowDeg.mp h
  rw [R.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [pderiv_monomial]
  by_cases h0 : m (f i) = 0
  · rw [h0, Nat.cast_zero, mul_zero, map_zero]
    exact Submodule.zero_mem _
  apply monomial_mem_lowDeg_of_weighted_sum_lt
  have hm' := hR m hm
  have e1 : m (f i) + ∑ j ∈ Finset.univ.erase i, m (f j) = ∑ j, m (f j) :=
    Finset.add_sum_erase _ (fun j => m (f j)) (Finset.mem_univ i)
  have e2 : (m - Finsupp.single (f i) 1 : σ →₀ ℕ) (f i) + ∑ j ∈ Finset.univ.erase i, (m - Finsupp.single (f i) 1 : σ →₀ ℕ) (f j) =
      ∑ j, (m - Finsupp.single (f i) 1 : σ →₀ ℕ) (f j) :=
    Finset.add_sum_erase _ (fun j => (m - Finsupp.single (f i) 1 : σ →₀ ℕ) (f j)) (Finset.mem_univ i)
  have le : ∑ j ∈ Finset.univ.erase i, (m - Finsupp.single (f i) 1 : σ →₀ ℕ) (f j) ≤ ∑ j ∈ Finset.univ.erase i, m (f j) :=
    Finset.sum_le_sum fun j _ => (Finsupp.tsub_apply _ _ _).trans_le (Nat.sub_le _ _)
  have gi : (m - Finsupp.single (f i) 1 : σ →₀ ℕ) (f i) = m (f i) - 1 := by
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
  omega

theorem pow_apply_eq_zero_of_lowDeg (D : Module.End K (MvPolynomial σ K)) (f : ι → σ)
    (hD : ∀ t R, R ∈ lowDeg f (t + 1) → D R ∈ lowDeg f t) :
    ∀ n R, R ∈ lowDeg f n → (D ^ n) R = 0 := by
  intro n
  induction n with
  | zero =>
    intro R hR
    rw [pow_zero]
    exact eq_zero_of_mem_lowDeg_zero hR
  | succ n ih =>
    intro R hR
    rw [pow_succ]
    exact ih _ (hD n R hR)

end

section
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]

theorem gdelta_apply (κ : I → J → K) (R : MvPolynomial (I ⊕ J) K) :
    gdelta κ R = ∑ i, ∑ j, κ i j • pderiv (Sum.inl i) (pderiv (Sum.inr j) R) := by
  unfold gdelta
  simp [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]

theorem gdelta_mem_lowDeg_inl (κ : I → J → K) {t : ℕ} {R : MvPolynomial (I ⊕ J) K}
    (h : R ∈ lowDeg (Sum.inl : I → I ⊕ J) (t + 1)) :
    gdelta κ R ∈ lowDeg (Sum.inl : I → I ⊕ J) t := by
  rw [gdelta_apply]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
  exact pderiv_mem_lowDeg_of_succ (f := (Sum.inl : I → I ⊕ J)) i (pderiv_mem_lowDeg _ h)

end

theorem vanL_holds : VanL := by
  unfold VanL
  intro K I J _ _ _ κ R n h
  exact pow_apply_eq_zero_of_lowDeg _ _ (fun t R h => gdelta_mem_lowDeg_inl κ h) n R (mem_lowDeg.mpr h)

end PI.WickFormula.Gen
