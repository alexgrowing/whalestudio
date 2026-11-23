import Mathlib

theorem _root_.UpperTheory.KN.mem_range_semilinear_of_values_mem_range :
    ∀ (K M N V U I J : Type) [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module ℂ N] [AddCommGroup V] [Module K V] [AddCommGroup U] [Module ℂ U]
      (σ : K →+* ℂ) (jm : M →ₛₗ[σ] N) (ev : N →ₗ[ℂ] (I → U)) (c0 : V →ₛₗ[σ] U) (b : Module.Basis J K V),
      Submodule.span ℂ (Set.range jm) = ⊤ → Function.Injective ev → LinearIndependent ℂ (fun i => c0 (b i)) →
      (∀ m h, ev (jm m) h ∈ Set.range c0) → ∀ f : N, (∀ h, ev f h ∈ Set.range c0) → f ∈ Set.range jm := by
  intro K M N V U I J _ _ _ _ _ _ _ _ _ σ jm ev c0 b hspan hev hli hjm f hf
  classical
  letI : Algebra K ℂ := σ.toAlgebra
  have hσ : ∀ k : K, algebraMap K ℂ k = σ k := fun k => rfl
  obtain ⟨lam, hlam⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K ℂ)
    (LinearMap.ker_eq_bot.mpr (algebraMap K ℂ).injective)
  have lam_mul : ∀ k z, lam (σ k * z) = k * lam z := by
    intro k z
    rw [← hσ, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have lam_one : lam 1 = 1 := by
    have := LinearMap.congr_fun hlam 1
    simpa using this
  let B := Module.Basis.span hli
  obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_extend (B.repr.toLinearMap)
  have hΨb : ∀ j, Ψ (c0 (b j)) = Finsupp.single j 1 := by
    intro j
    have h1 := LinearMap.congr_fun hΨ (B j)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
      B.repr_self] at h1
    rwa [Module.Basis.span_apply] at h1
  have hΨv : ∀ v j, Ψ (c0 v) j = σ (b.repr v j) := by
    intro v j
    conv_lhs => rw [← b.linearCombination_repr v, Finsupp.linearCombination_apply]
    simp [map_finsuppSum, hΨb, Finsupp.single_apply, Finsupp.sum_apply]
    intro h0
    rw [h0, map_zero]
  let R : U →+ V := b.repr.symm.toLinearMap.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom lam.toAddMonoidHom).comp Ψ.toAddMonoidHom)
  have hRrepr : ∀ u j, b.repr (R u) j = lam (Ψ u j) := by
    intro u j
    simp [R]
  have KR : ∀ (z : ℂ) (v : V), R (z • c0 v) = lam z • v := by
    intro z v
    apply b.repr.injective
    ext j
    rw [hRrepr, map_smul, Finsupp.smul_apply, hΨv, smul_eq_mul, mul_comm, lam_mul,
      map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  have Rc0 : ∀ v, R (c0 v) = v := by
    intro v
    have := KR 1 v
    rwa [one_smul, lam_one, one_smul] at this
  have hf' : f ∈ Submodule.span ℂ (Set.range jm) := hspan ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hf'
  refine ⟨c.sum fun m a => lam a • m, ?_⟩
  apply hev
  funext h
  obtain ⟨w, hw⟩ := hf h
  have hu : ∀ m, c0 (R (ev (jm m) h)) = ev (jm m) h := by
    intro m
    obtain ⟨v, hv⟩ := hjm m h
    rw [← hv, Rc0]
  have e1 : ev (jm (c.sum fun m a => lam a • m)) h = c.sum fun m a => σ (lam a) • ev (jm m) h := by
    simp [Finsupp.sum, map_sum, map_smulₛₗ, Finset.sum_apply]
  have e2 : ev (c.sum fun m a => a • jm m) h = c.sum fun m a => a • ev (jm m) h := by
    simp [Finsupp.sum, map_sum, Finset.sum_apply]
  have e3 : c0 (R (c.sum fun m a => a • ev (jm m) h)) = c.sum fun m a => σ (lam a) • ev (jm m) h := by
    simp only [Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    conv_lhs => rw [← hu m]
    rw [KR, map_smulₛₗ, hu m]
  rw [e1, ← e3, ← e2, ← hw, Rc0]
