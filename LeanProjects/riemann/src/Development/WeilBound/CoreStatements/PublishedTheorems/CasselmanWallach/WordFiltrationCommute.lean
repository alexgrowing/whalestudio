import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace EigenSumRepresentation

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type}

lemma inner_basis {b : Module.Basis ι ℂ V} (hb : Orthonormal ℂ b) (i : ι) (y : V) :
    inner ℂ (b i) y = b.repr y i := by
  have h := hb.inner_right_finsupp (b.repr y) i
  rwa [b.linearCombination_repr] at h

lemma repr_sum {b : Module.Basis ι ℂ V} (T : Finset ι) (y : V) (hy : (b.repr y).support ⊆ T) :
    y = ∑ j ∈ T, b.repr y j • b j := by
  conv_lhs => rw [← b.linearCombination_repr y]
  rw [Finsupp.linearCombination_apply]
  exact Finsupp.sum_of_support_subset _ hy _ (fun i _ => zero_smul ℂ (b i))

lemma inner_h {b : Module.Basis ι ℂ V} (hb : Orthonormal ℂ b) (f : V →ₗ[ℂ] ℂ) (T : Finset ι) (y : V)
    (hy : (b.repr y).support ⊆ T) :
    inner ℂ (∑ j ∈ T, starRingEnd ℂ (f (b j)) • b j) y = f y := by
  rw [sum_inner]
  conv_rhs => rw [repr_sum (b := b) T y hy, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_basis hb, map_smul, smul_eq_mul, starRingEnd_self_apply, mul_comm]

lemma inner_fc {b : Module.Basis ι ℂ V} (hb : Orthonormal ℂ b) (μ : ι → ℝ) (φ : ℝ → ℝ) (S : Finset ι)
    (hS : ∀ i, i ∉ S → φ (μ i) = 0) (y : V) :
    inner ℂ y (fc b μ φ y) = ∑ i ∈ S, ((φ (μ i) * ‖b.repr y i‖ ^ 2 : ℝ) : ℂ) := by
  classical
  have hyU : (b.repr y).support ⊆ (b.repr y).support ∪ S := Finset.subset_union_left
  have hfc : fc b μ φ y = ∑ j ∈ (b.repr y).support ∪ S, b.repr y j • ((φ (μ j) : ℂ) • b j) := by
    conv_lhs => rw [repr_sum (b := b) _ y hyU]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, fc, Module.Basis.constr_basis]
  have key : ∀ j, inner ℂ y (b.repr y j • ((φ (μ j) : ℂ) • b j)) = ((φ (μ j) * ‖b.repr y j‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    rw [inner_smul_right, inner_smul_right, ← inner_conj_symm, inner_basis hb]
    push_cast
    rw [← Complex.mul_conj']
    ring
  rw [hfc, inner_sum, Finset.sum_congr rfl (fun j _ => key j)]
  symm
  apply Finset.sum_subset Finset.subset_union_right
  intro j _ hj
  rw [hS j hj]
  simp

lemma beta_sum {E : Fin n → Fin n → Module.End ℂ V} (A : Module.End ℂ V) {κ : Type} (s : Finset κ) (v : κ → V) :
    beta ε E A (∑ k ∈ s, v k) (∑ k ∈ s, v k) = ∑ l ∈ s, ∑ k ∈ s, beta ε E A (v k) (v l) := by
  simp only [beta, map_sum, sum_inner, inner_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]

lemma eig_sum {E : Fin n → Fin n → Module.End ℂ V} {b : Module.Basis ι ℂ V} {μ : ι → ℝ}
    (heig : ∀ i, Eig ε E (μ i) (b i)) (s : Finset ι) (c : ι → ℂ) (ν : ℝ) (hs : ∀ j ∈ s, μ j = ν) :
    Eig ε E ν (∑ j ∈ s, c j • b j) := by
  unfold Eig
  rw [map_sum, smul_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [map_smul, show casimirK ε E (b j) = _ from heig j, hs j hj, smul_comm]

lemma mem_nc_swap {p : Fin n × Fin n} (hp : p ∈ nc ε) : p.swap ∈ nc ε := by
  simp only [nc, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact Ne.symm hp

end EigenSumRepresentation

open EigenSumRepresentation in
theorem basis_sum_of_orthogonality : A0 → FunctionalCalculusLaws → EigenspacesOrthogonalAlt → BasisSumAsFormValues := by
  intro _ _ h11c n ε V _ _ E hM ι b μ hB φ S hS
  classical
  set T : Finset ι := S ∪ S.biUnion (fun i => (nc ε).biUnion (fun p => (b.repr (E p.1 p.2 (b i))).support)) with hT
  refine ⟨T, Finset.subset_union_left, fun f => ?_⟩
  have hsupp : ∀ i ∈ S, ∀ p ∈ nc ε, (b.repr (E p.1 p.2 (b i))).support ⊆ T := by
    intro i hi p hp j hj
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.2 ⟨i, hi, Finset.mem_biUnion.2 ⟨p, hp, hj⟩⟩
  set H : V := ∑ j ∈ T, starRingEnd ℂ (f (b j)) • b j with hH
  have hinner : ∀ y, (b.repr y).support ⊆ T → inner ℂ H y = f y := fun y hy => inner_h hB.on f T y hy
  have hfib : ∑ ν ∈ image μ T, (∑ j ∈ T with μ j = ν, starRingEnd ℂ (f (b j)) • b j) = H :=
    Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_image_of_mem μ hj) _
  have heig : ∀ ν, Eig ε E ν (∑ j ∈ T with μ j = ν, starRingEnd ℂ (f (b j)) • b j) := fun ν =>
    eig_sum hB.eig _ (fun j => starRingEnd ℂ (f (b j))) ν (fun j hj => (Finset.mem_filter.1 hj).2)
  have hdiag : ∑ ν ∈ image μ T, beta ε E (fc b μ φ) (∑ j ∈ T with μ j = ν, starRingEnd ℂ (f (b j)) • b j)
      (∑ j ∈ T with μ j = ν, starRingEnd ℂ (f (b j)) • b j) = beta ε E (fc b μ φ) H H := by
    rw [← hfib, beta_sum (v := fun ν => ∑ j ∈ T with μ j = ν, starRingEnd ℂ (f (b j)) • b j)]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.sum_eq_single_of_mem l hl]
    intro k _ hk
    exact h11c n ε V E hM ι b μ hB φ k l _ _ hk (heig k) (heig l)
  rw [← Complex.re_sum, hdiag]
  have hterm : ∀ p ∈ nc ε, ∀ i ∈ S, ‖b.repr (E p.1 p.2 H) i‖ = ‖f (E p.2 p.1 (b i))‖ := by
    intro p hp i hi
    have hsw : (p.2, p.1) ∈ nc ε := mem_nc_swap hp
    have hsign : adjSign ε p.1 p.2 = -1 := by
      simp only [nc, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp [adjSign, hp]
    rw [← inner_basis hB.on, ← inner_conj_symm, hM.uni p.1 p.2 H (b i), hinner _ (hsupp i hi _ hsw), hsign]
    simp
  have hbeta : beta ε E (fc b μ φ) H H =
      ∑ p ∈ nc ε, ∑ i ∈ S, ((φ (μ i) * ‖f (E p.2 p.1 (b i))‖ ^ 2 : ℝ) : ℂ) := by
    unfold beta
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [inner_fc hB.on μ φ S hS]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hterm p hp i hi]
  rw [hbeta, Finset.sum_comm]
  simp only [Complex.re_sum, Complex.ofReal_re]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact Finset.sum_nbij' Prod.swap Prod.swap (fun p hp => mem_nc_swap hp) (fun p hp => mem_nc_swap hp)
    (fun p _ => rfl) (fun p _ => rfl) (fun p _ => rfl)

end PositivityTheory.CW

end
