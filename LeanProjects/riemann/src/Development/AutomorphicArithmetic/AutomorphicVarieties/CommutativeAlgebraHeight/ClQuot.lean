import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem maximalIdeal_map_eq_of_surjective {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (f : R →+* R') (hf : Function.Surjective f) : (maximalIdeal R).map f = maximalIdeal R' := by
  have hk : RingHom.ker f ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f)
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (f := f) hf (I := maximalIdeal R)
      (maximalIdeal.isMaximal R) with h | h
  · exfalso
    have h1 : (1 : R') ∈ (maximalIdeal R).map f := h ▸ Submodule.mem_top
    obtain ⟨y, hy, hy1⟩ := (Ideal.mem_map_iff_of_surjective f hf).1 h1
    have hker : 1 - y ∈ RingHom.ker f := by simp [RingHom.mem_ker, hy1]
    have h2 := Ideal.add_mem _ (hk hker) hy
    rw [sub_add_cancel] at h2
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h2)
  · exact IsLocalRing.eq_maximalIdeal h

private theorem isLocalHom_of_surjective {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (f : R →+* R') (hf : Function.Surjective f) : IsLocalHom f := by
  refine ⟨fun x hx => ?_⟩
  by_contra h
  have hx' : x ∈ maximalIdeal R := h
  have : f x ∈ maximalIdeal R' := by
    rw [← maximalIdeal_map_eq_of_surjective f hf]
    exact Ideal.mem_map_of_mem f hx'
  exact this hx

private theorem smodEq_ideal_pow_smul_univ_iff_sub_mem {A : Type} [CommRing A] (I : Ideal A) (n : ℕ) (a b : A) :
    a ≡ b [SMOD (I ^ n • ⊤ : Submodule A A)] ↔ a - b ∈ I ^ n := by
  simp [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem UpperTheory.V.CA.cl_quot :
    ∀ (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R] [IsLocalRing R] (R' : Type) [CommRing R'] [Algebra O R'] [IsLocalRing R'] (p : R →ₐ[O] R'), Function.Surjective p → IsCL O R → IsCL O R' := by
  intro O _ R _ _ _ R' _ _ _ p hp hR
  have hpr : Function.Surjective (p : R →+* R') := hp
  haveI : IsLocalHom (p : R →+* R') := isLocalHom_of_surjective _ hpr
  haveI := hR.noeth
  haveI : IsNoetherianRing R' := isNoetherianRing_of_surjective R R' (p : R →+* R') hpr
  haveI := hR.complete
  have hm : maximalIdeal R' = (maximalIdeal R).map (p : R →+* R') := (maximalIdeal_map_eq_of_surjective _ hpr).symm
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · haveI : IsHausdorff (maximalIdeal R') R' := inferInstance
    refine { toIsHausdorff := inferInstance, toIsPrecomplete := ⟨fun f hf => ?_⟩ }
    have hd : ∀ n, ∃ d ∈ maximalIdeal R ^ n, p d = f (n + 1) - f n := by
      intro n
      have h0 := (smodEq_ideal_pow_smul_univ_iff_sub_mem _ _ _ _).1 (hf (Nat.le_succ n))
      rw [hm, ← Ideal.map_pow] at h0
      obtain ⟨d, hd, hd'⟩ := (Ideal.mem_map_iff_of_surjective _ hpr).1 (neg_mem h0)
      refine ⟨d, hd, ?_⟩
      rw [neg_sub] at hd'
      exact hd'
    choose d hdm hdp using hd
    obtain ⟨y0, hy0⟩ := hp (f 0)
    have hy : ∀ n, p (y0 + ∑ k ∈ Finset.range n, d k) = f n := by
      intro n
      induction n with
      | zero => simp [hy0]
      | succ n ih =>
        rw [Finset.sum_range_succ, ← add_assoc, map_add, ih, hdp]
        ring
    have hcauchy : ∀ {m n : ℕ}, m ≤ n →
        (y0 + ∑ k ∈ Finset.range m, d k) ≡ (y0 + ∑ k ∈ Finset.range n, d k)
          [SMOD (maximalIdeal R ^ m • ⊤ : Submodule R R)] := by
      intro m n hmn
      rw [smodEq_ideal_pow_smul_univ_iff_sub_mem]
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        have e : (y0 + ∑ k ∈ Finset.range m, d k) - (y0 + ∑ k ∈ Finset.range (n + 1), d k) =
            ((y0 + ∑ k ∈ Finset.range m, d k) - (y0 + ∑ k ∈ Finset.range n, d k)) - d n := by
          rw [Finset.sum_range_succ]
          ring
        rw [e]
        exact Ideal.sub_mem _ ih (Ideal.pow_le_pow_right hmn (hdm n))
    obtain ⟨L, hL⟩ := (inferInstance : IsPrecomplete (maximalIdeal R) R).prec'
      (fun n => y0 + ∑ k ∈ Finset.range n, d k) hcauchy
    refine ⟨p L, fun n => ?_⟩
    rw [smodEq_ideal_pow_smul_univ_iff_sub_mem, hm, ← Ideal.map_pow, ← hy n, ← map_sub]
    exact Ideal.mem_map_of_mem (p : R →+* R') ((smodEq_ideal_pow_smul_univ_iff_sub_mem _ _ _ _).1 (hL n))
  · refine ⟨fun x hx => ?_⟩
    have e : algebraMap O R' x = (p : R →+* R') (algebraMap O R x) := (p.commutes x).symm
    rw [e] at hx
    exact hR.isLocalHom.map_nonunit _ (IsLocalHom.map_nonunit _ hx)
  · let L : ResidueField R →ₗ[O] ResidueField R' :=
      { toFun := IsLocalRing.ResidueField.map (p : R →+* R')
        map_add' := map_add _
        map_smul' := by
          intro o x
          obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
          simp only [Algebra.smul_def, map_mul, RingHom.id_apply]
          congr 1
          rw [IsScalarTower.algebraMap_apply O R (ResidueField R),
            IsScalarTower.algebraMap_apply O R' (ResidueField R')]
          change IsLocalRing.ResidueField.map _ (residue R _) = residue R' _
          rw [IsLocalRing.ResidueField.map_residue]
          simp }
    have hL : Function.Surjective L := by
      intro z
      obtain ⟨y', rfl⟩ := IsLocalRing.residue_surjective z
      obtain ⟨y, rfl⟩ := hpr y'
      exact ⟨IsLocalRing.residue R y, IsLocalRing.ResidueField.map_residue _ _⟩
    haveI := hR.res_fin
    exact Module.Finite.of_surjective L hL
