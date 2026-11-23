import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.DividedPowerIntegrals.GenDefs

open MvPolynomial

namespace PI.DivPowInteg.Gen

section
variable {K σ ι : Type} [CommRing K] [Fintype ι]

noncomputable def lowDeg (f : ι → σ) (t : ℕ) : Submodule K (MvPolynomial σ K) :=
  restrictSupport K {m | ∑ i, m (f i) < t}

theorem mem_lowDeg {f : ι → σ} {t : ℕ} {R : MvPolynomial σ K} :
    R ∈ lowDeg f t ↔ ∀ m ∈ R.support, ∑ i, m (f i) < t := by
  unfold lowDeg
  rw [mem_restrictSupport_iff]
  exact ⟨fun h m hm => h (Finset.mem_coe.mpr hm), fun h m hm => h m (Finset.mem_coe.mp hm)⟩

theorem eq_zero_of_mem_lowDeg_zero {f : ι → σ} {R : MvPolynomial σ K}
    (h : R ∈ lowDeg f 0) : R = 0 := by
  rw [mem_lowDeg] at h
  by_contra hR
  obtain ⟨m, hm⟩ := Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.mp hR)
  exact absurd (h m hm) (Nat.not_lt_zero _)

theorem pderiv_mem_lowDeg {f : ι → σ} {t : ℕ} (k : σ) {R : MvPolynomial σ K}
    (h : R ∈ lowDeg f t) : pderiv k R ∈ lowDeg f t := by
  rw [mem_lowDeg] at h
  rw [R.as_sum, map_sum]
  refine Submodule.sum_mem _ (fun m hm => ?_)
  rw [pderiv_monomial, mem_lowDeg]
  intro m' hm'
  rw [Finset.mem_singleton.mp (support_monomial_subset hm')]
  calc ∑ i, (m - Finsupp.single k 1 : σ →₀ ℕ) (f i) ≤ ∑ i, m (f i) :=
        Finset.sum_le_sum (fun i _ => by rw [Finsupp.tsub_apply]; exact Nat.sub_le _ _)
    _ < t := h m hm

theorem pderiv_mem_lowDeg_of_succ {f : ι → σ} {t : ℕ} (i : ι) {R : MvPolynomial σ K}
    (h : R ∈ lowDeg f (t + 1)) : pderiv (f i) R ∈ lowDeg f t := by
  rw [mem_lowDeg] at h
  rw [R.as_sum, map_sum]
  refine Submodule.sum_mem _ (fun m hm => ?_)
  rw [pderiv_monomial]
  by_cases h0 : m (f i) = 0
  · rw [h0]
    simp
  · rw [mem_lowDeg]
    intro m' hm'
    rw [Finset.mem_singleton.mp (support_monomial_subset hm')]
    have hlt := h m hm
    have key : ∑ i', (m - Finsupp.single (f i) 1 : σ →₀ ℕ) (f i') + 1 ≤ ∑ i', m (f i') := by
      classical
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      have h1 : (m - Finsupp.single (f i) 1 : σ →₀ ℕ) (f i) + 1 = m (f i) := by
        rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
        omega
      have h2 : ∑ x ∈ Finset.univ.erase i, (m - Finsupp.single (f i) 1 : σ →₀ ℕ) (f x) ≤
          ∑ x ∈ Finset.univ.erase i, m (f x) :=
        Finset.sum_le_sum (fun x _ => by rw [Finsupp.tsub_apply]; exact Nat.sub_le _ _)
      omega
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
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (hD n R hR)

end

section
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]

theorem gdelta_apply (κ : I → J → K) (R : MvPolynomial (I ⊕ J) K) :
    gdelta κ R = ∑ i, ∑ j, κ i j • pderiv (Sum.inl i) (pderiv (Sum.inr j) R) := by
  simp [gdelta, LinearMap.sum_apply]

theorem gdelta_mem_lowDeg_inl (κ : I → J → K) {t : ℕ} {R : MvPolynomial (I ⊕ J) K}
    (h : R ∈ lowDeg (Sum.inl : I → I ⊕ J) (t + 1)) :
    gdelta κ R ∈ lowDeg (Sum.inl : I → I ⊕ J) t := by
  rw [gdelta_apply]
  refine Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ ?_))
  exact pderiv_mem_lowDeg_of_succ (f := Sum.inl) i (pderiv_mem_lowDeg (Sum.inr j) h)

theorem gdelta_mem_lowDeg_inr (κ : I → J → K) {t : ℕ} {R : MvPolynomial (I ⊕ J) K}
    (h : R ∈ lowDeg (Sum.inr : J → I ⊕ J) (t + 1)) :
    gdelta κ R ∈ lowDeg (Sum.inr : J → I ⊕ J) t := by
  rw [gdelta_apply]
  refine Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ ?_))
  exact pderiv_mem_lowDeg (Sum.inl i) (pderiv_mem_lowDeg_of_succ (f := Sum.inr) j h)

end

theorem vanL_holds : VanL := by
  intro K I J _ _ _ κ R n h
  exact pow_apply_eq_zero_of_lowDeg (gdelta κ) Sum.inl (fun t R hR => gdelta_mem_lowDeg_inl κ hR) n R
    (mem_lowDeg.mpr h)

theorem vanR_holds : VanR := by
  intro K I J _ _ _ κ R n h
  exact pow_apply_eq_zero_of_lowDeg (gdelta κ) Sum.inr (fun t R hR => gdelta_mem_lowDeg_inr κ hR) n R
    (mem_lowDeg.mpr h)

end PI.DivPowInteg.Gen
