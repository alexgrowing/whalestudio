import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem dat_g_pow_apply_ofMul_eq_actU_inv_pow {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F]
    (γ : F ≃ₐ[L] F) (a : ℕ) (D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ)) (hD : IsDat γ a D)
    (k : ℕ) (α : Fˣ) :
    (D.g ^ k) (Additive.ofMul α) = Additive.ofMul (actU (γ⁻¹ ^ k) α) := by
  induction k generalizing α with
  | zero => simp [actU]; rfl
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, hD.g_eq, ih]
    congr 1

private theorem dat_nm_apply_ofMul_eq_ofMul_nrm {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F]
    (γ : F ≃ₐ[L] F) (a : ℕ) (D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ)) (hD : IsDat γ a D)
    (α : Fˣ) :
    D.nm (Additive.ofMul α) = Additive.ofMul (nrm γ a α) := by
  simp only [Dat.nm, LinearMap.sum_apply, LinearMap.smul_apply, nrm, ofMul_prod, ofMul_pow, hD.n_eq,
    hD.a_eq, dat_g_pow_apply_ofMul_eq_actU_inv_pow γ a D hD]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ orderOf γ := (Finset.mem_range.mp hj).le
  have hinv : (γ⁻¹) ^ (orderOf γ - j) = γ ^ j := by
    rw [inv_pow]
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, Nat.sub_add_cancel hj', pow_orderOf_eq_one]
  rw [hinv]
  push_cast
  exact natCast_zsmul _ _

theorem UpperTheory.V.ZK.Ct.fewLe :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F) (a s q B : ℕ) (D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ)), IsDat γ a D → Few γ a s q B → ∀ f : D.W →ₗ[ℤ] Additive Fˣ ⧸ mt (Additive Fˣ) q, (∀ y : D.U, f (Submodule.Quotient.mk y) = Submodule.Quotient.mk ((s : ℤ) • D.nm y)) → Finite D.W → Nat.card (LinearMap.range f) ≤ B := by
  intro L F _ _ _ _ _ γ a s q B D hD hF f hf hW
  classical
  haveI : Finite (LinearMap.range f) := Finite.of_surjective _ f.surjective_rangeRestrict
  haveI := Fintype.ofFinite (LinearMap.range f)
  choose w hw using fun z : LinearMap.range f => LinearMap.mem_range.mp z.2
  choose u hu using fun z : LinearMap.range f => Submodule.Quotient.mk_surjective _ (w z)
  have hφ : ∀ z, f (Submodule.Quotient.mk (u z)) = z := by
    intro z
    rw [hu, hw]
  let φ : LinearMap.range f → Fˣ := fun z => Additive.toMul ((u z : D.U) : Additive Fˣ)
  have hinj : Function.Injective φ := by
    intro z z' h
    have h' : u z = u z' := Subtype.ext (Additive.toMul.injective h)
    apply Subtype.ext
    rw [← hφ z, ← hφ z', h']
  have key := hF (Finset.univ.image φ) ?_ ?_
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ← Nat.card_eq_fintype_card] at key
    exact key
  · intro α hα
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hα
    obtain ⟨𝔡, h𝔡⟩ := LinearMap.mem_range.mp (u z).2
    refine ⟨𝔡, fun P => ?_⟩
    have hP := congrArg (fun x => x P) h𝔡
    have hd : ordP P (φ z) = D.d ((u z : D.U) : Additive Fˣ) P := (hD.d_eq _ P).symm
    rw [hd, ← hP]
    simp [Dat.delI, hD.gI_eq, hD.a_eq]
  · intro α hα α' hα' ⟨δ, hδ⟩
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hα
    obtain ⟨z', -, rfl⟩ := Finset.mem_image.mp hα'
    congr 1
    apply Subtype.ext
    rw [← hφ z, ← hφ z', hf, hf, Submodule.Quotient.eq]
    apply Submodule.mem_sup_left
    refine LinearMap.mem_range.mpr ⟨Additive.ofMul δ, ?_⟩
    have e := congrArg Additive.ofMul hδ
    rw [ofMul_mul, ofMul_pow, ofMul_pow, ofMul_pow] at e
    have e1 := dat_nm_apply_ofMul_eq_ofMul_nrm γ a D hD (φ z)
    have e2 := dat_nm_apply_ofMul_eq_ofMul_nrm γ a D hD (φ z')
    change D.nm (u z : Additive Fˣ) = _ at e1
    change D.nm (u z' : Additive Fˣ) = _ at e2
    rw [e1, e2, natCast_zsmul, natCast_zsmul, e]
    simp
