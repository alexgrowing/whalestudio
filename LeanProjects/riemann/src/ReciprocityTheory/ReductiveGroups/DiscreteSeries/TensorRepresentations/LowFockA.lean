import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFPrimeA

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem lfa_mul_of_not_disjoint (s t : Finset (Fin (n * n))) (h : ¬ Disjoint s t) :
    fockBasis n s * fockBasis n t = 0 := by
  exact ExteriorAlgebra.basis_mul_of_not_disjoint _ (Set.powersetCard.ofCard (rfl : s.card = s.card))
    (Set.powersetCard.ofCard (rfl : t.card = t.card)) h

theorem eq_sign_smul_of_intUnit {A : Type*} [AddCommGroup A] [Module ℂ A] (u : ℤˣ) (x y : A) (h : x = u • y) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧ x = σ • y := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact ⟨1, Or.inl rfl, by simpa using h⟩
  · exact ⟨-1, Or.inr rfl, by simpa using h⟩

theorem lfa_mul_of_disjoint (s t : Finset (Fin (n * n))) (h : Disjoint s t) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧ fockBasis n s * fockBasis n t = σ • fockBasis n (s ∪ t) := by
  have hm := ExteriorAlgebra.basis_mul_of_disjoint ((Pi.basisFun ℂ (Fin n × Fin n)).reindex finProdFinEquiv)
    (Set.powersetCard.ofCard (rfl : s.card = s.card)) (Set.powersetCard.ofCard (rfl : t.card = t.card)) h
  obtain ⟨σ, hσ, h'⟩ := eq_sign_smul_of_intUnit _ _ _ hm
  refine ⟨σ, hσ, h'.trans ?_⟩
  exact congrArg (fun U => σ • fockBasis n U) (Finset.disjUnion_eq_union s t h)

theorem lfa_basis_list (S : Finset (Fin (n * n))) :
    fockBasis n S = ((List.ofFn fun i => finProdFinEquiv.symm (S.orderEmbOfFin rfl i)).map
      fun y => ExteriorAlgebra.ι ℂ (Pi.single y (1 : ℂ))).prod := by
  rw [fockBasis, ExteriorAlgebra.basis_apply_ofCard _ (rfl : S.card = S.card), ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_apply, List.map_ofFn]
  congr 2
  funext i
  simp [Set.powersetCard.ofFinEmbEquiv_symm_apply]

theorem lf_basis_singleton (x : Fin n × Fin n) :
    fockBasis n {finProdFinEquiv x} = ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ)) := by
  rw [fockBasis, ExteriorAlgebra.basis_apply_ofCard _ (Finset.card_singleton _), ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_apply]
  simp [Set.powersetCard.ofFinEmbEquiv_symm_apply, Set.powersetCard.val_ofCard]

theorem lfa_cp_apply (x : Fin n × Fin n) (v : Fock n) :
    cpFock x.1 x.2 v = fockBasis n {finProdFinEquiv x} * v := by
  rw [lf_basis_singleton]
  rfl

theorem lfa_cm_list (x : Fin n × Fin n) (l : List (Fin n × Fin n)) (hx : x ∉ l) :
    cmFock x.1 x.2 (l.map fun y => ExteriorAlgebra.ι ℂ (Pi.single y (1 : ℂ))).prod = 0 := by
  induction l with
  | nil => simp [cmFock]
  | cons y l ih =>
    rw [List.mem_cons, not_or] at hx
    have ih' := ih hx.2
    simp only [cmFock] at ih' ⊢
    rw [List.map_cons, List.prod_cons, CliffordAlgebra.contractLeft_ι_mul, ih']
    simp [hx.1]

theorem lf_cp_basis_of_mem {x : Fin n × Fin n} {S : Finset (Fin (n * n))} (hx : finProdFinEquiv x ∈ S) :
    cpFock x.1 x.2 (fockBasis n S) = 0 := by
  rw [lfa_cp_apply]
  exact lfa_mul_of_not_disjoint _ _ (Finset.not_disjoint_iff.mpr ⟨_, Finset.mem_singleton_self _, hx⟩)

theorem lf_cm_basis_of_not_mem {x : Fin n × Fin n} {S : Finset (Fin (n * n))} (hx : finProdFinEquiv x ∉ S) :
    cmFock x.1 x.2 (fockBasis n S) = 0 := by
  rw [lfa_basis_list]
  apply lfa_cm_list
  intro hmem
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
  apply hx
  rw [← hi, Equiv.apply_symm_apply]
  exact Finset.orderEmbOfFin_mem S rfl i

theorem lf_cp_cm_basis {x : Fin n × Fin n} {S : Finset (Fin (n * n))} (hx : finProdFinEquiv x ∉ S) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
      cpFock x.1 x.2 (fockBasis n S) = σ • fockBasis n (insert (finProdFinEquiv x) S) ∧
      cmFock x.1 x.2 (fockBasis n (insert (finProdFinEquiv x) S)) = σ • fockBasis n S := by
  obtain ⟨σ, hσ, h⟩ := lfa_mul_of_disjoint {finProdFinEquiv x} S (Finset.disjoint_singleton_left.mpr hx)
  rw [← Finset.insert_eq] at h
  have hcp : cpFock x.1 x.2 (fockBasis n S) = σ • fockBasis n (insert (finProdFinEquiv x) S) := by
    rw [lfa_cp_apply, h]
  have hcmcp : cmFock x.1 x.2 (cpFock x.1 x.2 (fockBasis n S)) = fockBasis n S := by
    have h0 := lf_cm_basis_of_not_mem hx
    simp only [cpFock, cmFock, LinearMap.mulLeft_apply] at h0 ⊢
    rw [CliffordAlgebra.contractLeft_ι_mul, h0]
    simp
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  refine ⟨σ, hσ, hcp, ?_⟩
  rw [hcp, map_smul] at hcmcp
  calc cmFock x.1 x.2 (fockBasis n (insert (finProdFinEquiv x) S))
      = (σ * σ) • cmFock x.1 x.2 (fockBasis n (insert (finProdFinEquiv x) S)) := by rw [hσσ, one_smul]
    _ = σ • fockBasis n S := by rw [← smul_smul, hcmcp]

theorem lf_cm_basis_of_mem {x : Fin n × Fin n} {S : Finset (Fin (n * n))} (hx : finProdFinEquiv x ∈ S) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
      cmFock x.1 x.2 (fockBasis n S) = σ • fockBasis n (S.erase (finProdFinEquiv x)) ∧
      cpFock x.1 x.2 (fockBasis n (S.erase (finProdFinEquiv x))) = σ • fockBasis n S := by
  obtain ⟨σ, hσ, h1, h2⟩ := lf_cp_cm_basis (Finset.notMem_erase (finProdFinEquiv x) S)
  rw [Finset.insert_erase hx] at h1 h2
  exact ⟨σ, hσ, h2, h1⟩

theorem lf_num_basis (x : Fin n × Fin n) (S : Finset (Fin (n * n))) :
    cpFock x.1 x.2 (cmFock x.1 x.2 (fockBasis n S)) =
      if finProdFinEquiv x ∈ S then fockBasis n S else 0 := by
  split_ifs with hx
  · obtain ⟨σ, hσ, h1, h2⟩ := lf_cm_basis_of_mem hx
    rw [h1, map_smul, h2, smul_smul]
    rcases hσ with rfl | rfl <;> norm_num
  · rw [lf_cm_basis_of_not_mem hx, map_zero]

theorem lf_repr_cm_eq (x : Fin n × Fin n) (S T : Finset (Fin (n * n))) :
    (fockBasis n).repr (cmFock x.1 x.2 (fockBasis n S)) T =
      (fockBasis n).repr (cpFock x.1 x.2 (fockBasis n T)) S := by
  by_cases hT : finProdFinEquiv x ∈ T
  · rw [lf_cp_basis_of_mem hT, map_zero, Finsupp.zero_apply]
    by_cases hS : finProdFinEquiv x ∈ S
    · obtain ⟨σ, -, h1, -⟩ := lf_cm_basis_of_mem hS
      rw [h1, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero]
      intro h
      rw [← h] at hT
      exact Finset.notMem_erase _ _ hT
    · rw [lf_cm_basis_of_not_mem hS, map_zero, Finsupp.zero_apply]
  · obtain ⟨τ, -, h1, h2⟩ := lf_cp_cm_basis hT
    rw [h1, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    by_cases hST : insert (finProdFinEquiv x) T = S
    · subst hST
      rw [if_pos rfl, h2, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_pos rfl]
    · rw [if_neg hST, smul_zero]
      by_cases hS : finProdFinEquiv x ∈ S
      · obtain ⟨σ, -, h3, -⟩ := lf_cm_basis_of_mem hS
        rw [h3, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero]
        intro h
        apply hST
        rw [← h, Finset.insert_erase hS]
      · rw [lf_cm_basis_of_not_mem hS, map_zero, Finsupp.zero_apply]

theorem lf_repr_cp_star (x : Fin n × Fin n) (S T : Finset (Fin (n * n))) :
    star ((fockBasis n).repr (cpFock x.1 x.2 (fockBasis n S)) T) =
      (fockBasis n).repr (cpFock x.1 x.2 (fockBasis n S)) T := by
  by_cases hS : finProdFinEquiv x ∈ S
  · rw [lf_cp_basis_of_mem hS]
    simp
  · obtain ⟨τ, hτ, h1, -⟩ := lf_cp_cm_basis hS
    rw [h1, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    split_ifs <;> rcases hτ with rfl | rfl <;> simp

end ReciprocityTheory.ChartRestriction.DS
