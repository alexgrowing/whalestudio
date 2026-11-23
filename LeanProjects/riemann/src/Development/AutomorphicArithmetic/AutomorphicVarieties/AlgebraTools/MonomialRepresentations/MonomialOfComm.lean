import Mathlib

open Polynomial Matrix

private theorem monomial_eigenbasis {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hA : A.charpoly.Separable) :
    ∃ (b : Module.Basis (Fin n) K (Fin n → K)) (l : Fin n → K), Function.Injective l ∧
      ∀ i, A *ᵥ b i = l i • b i := by
  classical
  have hnd : A.charpoly.roots.Nodup := Polynomial.nodup_roots hA
  have hcard : A.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, ← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e : A.charpoly.roots.toFinset ≃ Fin n := Finset.equivFinOfCardEq hcard
  let l : Fin n → K := fun i => (e.symm i : K)
  have hl : Function.Injective l := fun i j h => e.symm.injective (Subtype.ext h)
  have hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' A) (l i) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
    have := (e.symm i).2
    rw [Multiset.mem_toFinset] at this
    exact Polynomial.isRoot_of_mem_roots this
  choose v hv using fun i => (hev i).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' A) l hl v hv
  have hsp : Submodule.span K (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp)
  refine ⟨Module.Basis.mk hli hsp.ge, l, hl, fun i => ?_⟩
  rw [Module.Basis.mk_apply]
  have := (hv i).apply_eq_smul
  rwa [Matrix.toLin'_apply] at this

private theorem monomial_eigvec {K : Type} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (b : Module.Basis (Fin n) K (Fin n → K)) (l : Fin n → K)
    (hl : Function.Injective l) (hb : ∀ i, A *ᵥ b i = l i • b i) (v : Fin n → K) (c : K)
    (hv : A *ᵥ v = c • v) (j : Fin n) (hj : l j ≠ c) : b.repr v j = 0 := by
  classical
  have h1 : (b.coord j) ∘ₗ (Matrix.toLin' A) = l j • b.coord j := by
    refine b.ext fun i => ?_
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, hb, map_smul, LinearMap.smul_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
    split_ifs with h
    · rw [h]
    · simp
  have h2 := LinearMap.congr_fun h1 v
  simp only [LinearMap.comp_apply, Matrix.toLin'_apply, hv, map_smul, LinearMap.smul_apply,
      Module.Basis.coord_apply, smul_eq_mul] at h2
  have h3 : (l j - c) * b.repr v j = 0 := by rw [sub_mul, h2, sub_self]
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hj)

private theorem monomial_eigvec' {K : Type} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (b : Module.Basis (Fin n) K (Fin n → K)) (l : Fin n → K)
    (hl : Function.Injective l) (hb : ∀ i, A *ᵥ b i = l i • b i) (v : Fin n → K)
    (i : Fin n) (hv : A *ᵥ v = l i • v) : ∃ a : K, v = a • b i := by
  classical
  refine ⟨b.repr v i, b.ext_elem fun j => ?_⟩
  by_cases h : i = j
  · subst h; simp
  · rw [monomial_eigvec A b l hl hb v _ hv j (fun h' => h (hl h').symm)]
    simp [h]

theorem UpperTheory.V.AlgebraTools.monomialOfComm :
    ∀ (K G : Type) [Field K] [IsAlgClosed K] [Group G] (n : ℕ) (r : G →* Matrix (Fin n) (Fin n) K), Submodule.span K (Set.range r) = ⊤ →
      ∀ (N : Subgroup G) [N.Normal], (∀ g ∈ N, ∀ h ∈ N, r g * r h = r h * r g) → (∃ u ∈ N, (r u).charpoly.Separable) →
      ∃ (b : Module.Basis (Fin n) K (Fin n → K)) (π : G →* Equiv.Perm (Fin n)), N ≤ π.ker ∧
        (∀ g i, ∃ a : K, r g *ᵥ b i = a • b (π g i)) ∧ ∀ i j, ∃ g, π g i = j := by
  classical
  intro K G _ _ _ n r hspan N hN hcomm ⟨u, hu, hsep⟩
  obtain ⟨b, l, hl, hb⟩ := monomial_eigenbasis (r u) hsep
  have hne : ∀ g i, r g *ᵥ b i ≠ 0 := by
    intro g i h
    have : r g⁻¹ *ᵥ (r g *ᵥ b i) = b i := by
      rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
    rw [h, Matrix.mulVec_zero] at this
    exact b.ne_zero i this.symm
  have hNs : ∀ h ∈ N, ∀ i, ∃ a : K, r h *ᵥ b i = a • b i := by
    intro h hh i
    refine monomial_eigvec' (r u) b l hl hb _ i ?_
    rw [Matrix.mulVec_mulVec, hcomm u hu h hh, ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_smul]
  have hex : ∀ g i, ∃ j, ∃ a : K, r g *ᵥ b i = a • b j := by
    intro g i
    obtain ⟨c, hc⟩ := hNs (g⁻¹ * u * g⁻¹⁻¹) (hN.conj_mem u hu g⁻¹) i
    have hv : r u *ᵥ (r g *ᵥ b i) = c • (r g *ᵥ b i) := by
      rw [← Matrix.mulVec_smul, ← hc, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← map_mul,
        ← map_mul]
      congr 2
      group
    by_cases hc' : ∃ j, l j = c
    · obtain ⟨j, rfl⟩ := hc'
      exact ⟨j, monomial_eigvec' (r u) b l hl hb _ j hv⟩
    · exfalso
      apply hne g i
      refine b.ext_elem fun j => ?_
      rw [monomial_eigvec (r u) b l hl hb _ _ hv j (fun h => hc' ⟨j, h⟩)]
      simp
  choose f hf using hex
  have huniq : ∀ g i j (a : K), r g *ᵥ b i = a • b j → f g i = j := by
    intro g i j a h
    obtain ⟨a', ha'⟩ := hf g i
    by_contra hij
    have h1 := congrArg (fun v => b.repr v j) (h.symm.trans ha')
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, hij,
      if_true, if_false, smul_eq_mul, mul_one, mul_zero] at h1
    apply hne g i
    rw [h, h1, zero_smul]
  let F : G →* Function.End (Fin n) :=
    { toFun := f
      map_one' := funext fun i => huniq 1 i i 1 (by simp)
      map_mul' := fun g h => funext fun i => by
        obtain ⟨a, ha⟩ := hf h i
        obtain ⟨a', ha'⟩ := hf g (f h i)
        refine huniq (g * h) i (f g (f h i)) (a * a') ?_
        rw [map_mul, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_smul, ha', smul_smul] }
  have hπ : ∀ g i, F.toHomPerm g i = f g i := fun g i => rfl
  refine ⟨b, F.toHomPerm, ?_, ?_, ?_⟩
  · intro h hh
    rw [MonoidHom.mem_ker]
    ext i
    obtain ⟨a, ha⟩ := hNs h hh i
    rw [hπ, huniq h i i a ha]
    rfl
  · intro g i
    exact hf g i
  · intro i j
    by_contra hno
    push Not at hno
    let φ : Matrix (Fin n) (Fin n) K →ₗ[K] K :=
      { toFun := fun M => b.repr (M *ᵥ b i) j
        map_add' := fun M M' => by simp [Matrix.add_mulVec]
        map_smul' := fun c M => by simp [Matrix.smul_mulVec] }
    have hle : Submodule.span K (Set.range r) ≤ LinearMap.ker φ := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      obtain ⟨a, ha⟩ := hf g i
      have hij : f g i ≠ j := hno g
      change b.repr (r g *ᵥ b i) j = 0
      rw [ha]
      simp [hij]
    have hM : LinearMap.toMatrix' ((b.coord i).smulRight (b j)) ∈ LinearMap.ker φ :=
      hle (hspan ▸ Submodule.mem_top)
    change b.repr (LinearMap.toMatrix' ((b.coord i).smulRight (b j)) *ᵥ b i) j = 0 at hM
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix'] at hM
    simp at hM
