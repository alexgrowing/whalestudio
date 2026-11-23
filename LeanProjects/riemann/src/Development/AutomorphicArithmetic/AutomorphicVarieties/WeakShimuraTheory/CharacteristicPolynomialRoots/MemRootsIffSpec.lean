import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.LeKerPt

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem mem_roots_iff_spec {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (z : K) :
    z ∈ M.charpoly.roots ↔ z ∈ spectrum K M := by
  rw [mem_roots M.charpoly_monic.ne_zero, Matrix.mem_spectrum_iff_isRoot_charpoly]

private theorem roots_aeval {K : Type} [Field K] [IsAlgClosed K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (p : K[X]) (w : K)
    (hw : w ∈ (aeval M p).charpoly.roots) : ∃ z ∈ M.charpoly.roots, p.eval z = w := by
  rw [mem_roots_iff_spec] at hw
  have hnt : Nontrivial (Matrix (Fin n) (Fin n) K) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hw (isUnit_of_subsingleton _)
  rw [spectrum.map_polynomial_aeval_of_nonempty M p (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional K M)] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  exact ⟨z, (mem_roots_iff_spec M z).2 hz, rfl⟩

private theorem sum_eq_count {K : Type} [Field K] [DecidableEq K] (c : K) (hc : c ≠ 0) (s : Multiset K)
    (h : ∀ w ∈ s, w = 0 ∨ w = c) : s.sum = (s.count c : K) * c := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.sum_cons, ih (fun w hw => h w (Multiset.mem_cons_of_mem hw))]
    rcases h a (Multiset.mem_cons_self _ _) with rfl | rfl
    · rw [Multiset.count_cons_of_ne hc]; simp
    · rw [Multiset.count_cons_self]; push_cast; ring

theorem UpperTheory.V.Ws.Pu.cpAlg :
    ∀ {O K Γ S : Type} [CommRing O] [Field K] [CharZero K] [IsAlgClosed K] [Algebra O K] [Group Γ] {n : ℕ} (ρ : Γ →* GL (Fin n) K) (t : Finset S) (d : S → ℕ) (σ : ∀ i, Γ →* GL (Fin (d i)) K),
      (∀ g, (W.mat ρ g).charpoly = ∏ i ∈ t, (W.mat (σ i) g).charpoly) → ∀ (y : MonoidAlgebra O Γ), ∀ i ∈ t,
        ∀ z ∈ (MonoidAlgebra.lift O (Matrix (Fin (d i)) (Fin (d i)) K) Γ (W.mat (σ i)) y).charpoly.roots,
          z ∈ (MonoidAlgebra.lift O (Matrix (Fin n) (Fin n) K) Γ (W.mat ρ) y).charpoly.roots := by
  intro O K Γ S _ _ _ _ _ _ n ρ t d σ hcp y i hi z hz
  classical
  have h1 : ∀ g, (W.mat ρ g).trace = ∑ j ∈ t, (W.mat (σ j) g).trace := by
    intro g
    simp only [Matrix.trace_eq_sum_roots_charpoly]
    rw [hcp g, roots_prod _ _ (Finset.prod_ne_zero_iff.2 fun j _ => (Matrix.charpoly_monic _).ne_zero), Multiset.sum_bind]
    rfl
  have h2 : ∀ x : MonoidAlgebra O Γ, (MonoidAlgebra.lift O (Matrix (Fin n) (Fin n) K) Γ (W.mat ρ) x).trace =
      ∑ j ∈ t, (MonoidAlgebra.lift O (Matrix (Fin (d j)) (Fin (d j)) K) Γ (W.mat (σ j)) x).trace := by
    intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, Matrix.trace_add, ha, hb, Finset.sum_add_distrib]
    | single g a => simp only [MonoidAlgebra.lift_single, Matrix.trace_smul, h1, Finset.smul_sum]
  set M := MonoidAlgebra.lift O (Matrix (Fin n) (Fin n) K) Γ (W.mat ρ) y with hM
  set N := fun j => MonoidAlgebra.lift O (Matrix (Fin (d j)) (Fin (d j)) K) Γ (W.mat (σ j)) y with hN
  have h3 : ∀ p : K[X], (aeval M p).trace = ∑ j ∈ t, (aeval (N j) p).trace := by
    intro p
    induction p using Polynomial.induction_on' with
    | add a b ha hb => simp only [map_add, Matrix.trace_add, ha, hb, Finset.sum_add_distrib]
    | monomial k a =>
      have := h2 (y ^ k)
      simp only [map_pow] at this
      simp only [aeval_monomial, ← Algebra.smul_def, Matrix.trace_smul, hM, hN, this, Finset.smul_sum]
  by_contra hzM
  let T : Finset K := (M.charpoly.roots.toFinset ∪ t.biUnion fun j => (N j).charpoly.roots.toFinset).erase z
  let p : K[X] := ∏ w ∈ T, (X - C w)
  have hpz : p.eval z ≠ 0 := by
    simp only [p, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_ne_zero_iff.2 fun w hw => sub_ne_zero.2 (Finset.ne_of_mem_erase hw).symm
  have hpT : ∀ w ∈ T, p.eval w = 0 := by
    intro w hw
    simp only [p, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero hw (sub_self _)
  have hM0 : (aeval M p).trace = 0 := by
    rw [Matrix.trace_eq_sum_roots_charpoly]
    refine Multiset.sum_eq_zero fun w hw => ?_
    obtain ⟨u, hu, rfl⟩ := roots_aeval M p w hw
    refine hpT u (Finset.mem_erase.2 ⟨?_, Finset.mem_union_left _ (Multiset.mem_toFinset.2 hu)⟩)
    rintro rfl
    exact hzM hu
  have hNj : ∀ j ∈ t, (aeval (N j) p).trace = ((aeval (N j) p).charpoly.roots.count (p.eval z) : K) * p.eval z := by
    intro j hj
    rw [Matrix.trace_eq_sum_roots_charpoly]
    refine sum_eq_count _ hpz _ fun w hw => ?_
    obtain ⟨u, hu, rfl⟩ := roots_aeval (N j) p w hw
    by_cases huz : u = z
    · exact Or.inr (by rw [huz])
    · exact Or.inl (hpT u (Finset.mem_erase.2 ⟨huz, Finset.mem_union_right _
        (Finset.mem_biUnion.2 ⟨j, hj, Multiset.mem_toFinset.2 hu⟩)⟩))
  have h4 := h3 p
  rw [hM0, Finset.sum_congr rfl hNj, ← Finset.sum_mul, ← Nat.cast_sum] at h4
  have h5 := (mul_eq_zero.1 h4.symm).resolve_right hpz
  rw [Nat.cast_eq_zero, Finset.sum_eq_zero_iff] at h5
  have h6 := h5 i hi
  rw [Multiset.count_eq_zero] at h6
  apply h6
  rw [mem_roots_iff_spec]
  exact spectrum.subset_polynomial_aeval (N i) p ⟨z, (mem_roots_iff_spec _ z).1 hz, rfl⟩
