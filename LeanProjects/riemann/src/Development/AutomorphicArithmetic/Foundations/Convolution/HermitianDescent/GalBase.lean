import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NormAlmostAll

noncomputable section

open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

section

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {σ : R ≃ₐ[k] R} {q : ℕ}

private theorem sum_fixed (h : IsGal σ q) (r : R) :
    σ (∑ j ∈ Finset.range q, (σ ^ j) r) = ∑ j ∈ Finset.range q, (σ ^ j) r := by
  have h1 := Finset.sum_range_succ (fun j => (σ ^ j) r) q
  have h2 := Finset.sum_range_succ' (fun j => (σ ^ j) r) q
  rw [h1, h.pow, pow_zero] at h2
  rw [map_sum, add_right_cancel h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_succ', AlgEquiv.mul_apply]

private theorem exists_tr (h : IsGal σ q) :
    ∃ t : R →ₗ[k] k, ∀ r, algebraMap k R (t r) = ∑ j ∈ Finset.range q, (σ ^ j) r := by
  choose t ht using fun r => h.fix _ (sum_fixed h r)
  refine ⟨⟨⟨t, fun a b => h.inj ?_⟩, fun c a => h.inj ?_⟩, ht⟩
  · rw [map_add, ht, ht, ht, ← Finset.sum_add_distrib]
    simp only [map_add]
  · simp only [RingHom.id_apply, smul_eq_mul]
    rw [map_mul, ht, ht, Finset.mul_sum]
    simp only [Algebra.smul_def, map_mul, AlgEquiv.commutes]

private theorem dual (h : IsGal σ q) {s : ℕ} {x y : Fin s → R}
    (hxy : ∀ j < q, ∑ i, x i * (σ ^ j) (y i) = if j = 0 then 1 else 0) {t : R →ₗ[k] k}
    (ht : ∀ r, algebraMap k R (t r) = ∑ j ∈ Finset.range q, (σ ^ j) r) (r : R) :
    ∑ i, t (y i * r) • x i = r := by
  calc ∑ i, t (y i * r) • x i
      = ∑ i, ∑ j ∈ Finset.range q, x i * (σ ^ j) (y i) * (σ ^ j) r := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def, ht, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]; ring
    _ = ∑ j ∈ Finset.range q, (if j = 0 then 1 else 0) * (σ ^ j) r := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [← Finset.sum_mul, hxy j (Finset.mem_range.1 hj)]
    _ = r := by
        simp [h.pos]

private theorem pow_tmul (A : Type) [CommRing A] [Algebra k A] (σ : R ≃ₐ[k] R) (j : ℕ) (a : A) (r : R) :
    ((Algebra.TensorProduct.congr AlgEquiv.refl σ : A ⊗[k] R ≃ₐ[A] A ⊗[k] R) ^ j) (a ⊗ₜ r) =
      a ⊗ₜ (σ ^ j) r := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih]
    simp

end

theorem galBase : GalBase := by
  intro k R _ _ _ A _ _ σ q h
  obtain ⟨t, ht⟩ := exists_tr h
  obtain ⟨s, x, y, hxy⟩ := h.sep
  have hd := dual h hxy ht
  have hsplit : (Fintype.linearCombination k x).comp
      (LinearMap.pi fun i => t.comp (LinearMap.mulLeft k (y i))) = LinearMap.id := by
    ext r
    simpa [Fintype.linearCombination_apply] using hd r
  have hfin : Module.Finite k R :=
    Module.Finite.of_surjective (Fintype.linearCombination k x) fun r =>
      ⟨_, LinearMap.congr_fun hsplit r⟩
  have hproj : Module.Projective k R := Module.Projective.of_split _ _ hsplit
  obtain ⟨c, hc⟩ : ∃ c, t c = 1 := by
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
      (LinearMap.range t) (⊤ : Submodule k R) Module.Finite.fg_top (by
        intro r _
        rw [← hd r]
        exact Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem_smul (LinearMap.mem_range_self _ _) Submodule.mem_top)
    have h0 : r = 0 := h.inj (by
      rw [map_zero, Algebra.algebraMap_eq_smul_one]; exact hr0 1 Submodule.mem_top)
    obtain ⟨c, hc⟩ := hr
    exact ⟨-c, by rw [map_neg, hc, h0]; ring⟩
  refine ⟨hfin, hproj, ⟨fun m hm hm' => hm.ne_top ?_⟩, ?_⟩
  · have key : ∀ r ∈ m • (⊤ : Submodule k R), t r ∈ m := by
      intro r hr
      refine Submodule.smul_induction_on hr (fun a ha n _ => ?_) (fun a b ha hb => ?_)
      · rw [map_smul, smul_eq_mul]; exact m.mul_mem_right _ ha
      · rw [map_add]; exact m.add_mem ha hb
    rw [Ideal.eq_top_iff_one, ← hc]
    exact key c (by rw [hm']; exact Submodule.mem_top)
  · set τ : A ⊗[k] R ≃ₐ[A] A ⊗[k] R := Algebra.TensorProduct.congr AlgEquiv.refl σ with hτ
    have hp : ∀ j a r, (τ ^ j) (a ⊗ₜ r) = a ⊗ₜ (σ ^ j) r := pow_tmul A σ
    let p : A ⊗[k] R →ₗ[k] A :=
      (TensorProduct.rid k A).toLinearMap.comp ((t.comp (LinearMap.mulLeft k c)).lTensor A)
    have hpp : ∀ a r, p (a ⊗ₜ r) = t (c * r) • a := fun a r => by simp [p]
    refine ⟨h.pos, ?_, ?_, ?_, s, fun i => 1 ⊗ₜ x i, fun i => 1 ⊗ₜ y i, fun j hj => ?_⟩
    · refine AlgEquiv.ext fun z => ?_
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a r => rw [hp, h.pow]; rfl
      | add a b ha hb => rw [map_add, map_add, ha, hb]
    · refine Function.LeftInverse.injective (g := p) fun a => ?_
      rw [Algebra.TensorProduct.algebraMap_apply, hpp, mul_one, hc, one_smul]
      rfl
    · intro z hz
      have h1 : ∀ z, algebraMap A (A ⊗[k] R) (p z) =
          ∑ j ∈ Finset.range q, (τ ^ j) ((1 ⊗ₜ c) * z) := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul a r =>
          simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hp]
          rw [← TensorProduct.tmul_sum, ← ht, hpp, Algebra.TensorProduct.algebraMap_apply,
            Algebra.algebraMap_eq_smul_one (t (c * r)), ← TensorProduct.smul_tmul]
          rfl
        | add a b ha hb =>
          simp only [map_add, mul_add, ha, hb, Finset.sum_add_distrib]
      have h2 : ∀ j : ℕ, (τ ^ j) z = z := by
        intro j
        induction j with
        | zero => rfl
        | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, hz, ih]
      refine ⟨p z, ?_⟩
      rw [h1]
      simp only [map_mul, h2, hp]
      rw [← Finset.sum_mul, ← TensorProduct.tmul_sum, ← ht, hc, map_one,
        ← Algebra.TensorProduct.one_def, one_mul]
    · simp only [hp, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [← TensorProduct.tmul_sum, hxy j hj]
      split_ifs
      · rfl
      · exact TensorProduct.tmul_zero _ _

end UpperTheory.ConvolutionTheory.D
