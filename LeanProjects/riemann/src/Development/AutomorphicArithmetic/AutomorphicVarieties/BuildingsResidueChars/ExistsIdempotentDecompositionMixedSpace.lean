import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem one_tmul_add_tmul_mul_I_eq_smul_of_sq_eq_one {R : Type} [CommRing R] [Algebra ℝ R] (g : ℂ →ₗ[ℝ] R) (σ z : ℂ)
    (hσ : σ * σ = 1) :
    (1 : ℂ) ⊗ₜ[ℝ] g z + (σ * Complex.I) ⊗ₜ[ℝ] g (z * Complex.I) =
      ((z.re : ℂ) - σ * z.im * Complex.I) •
        ((1 : ℂ) ⊗ₜ[ℝ] g 1 + (σ * Complex.I) ⊗ₜ[ℝ] g Complex.I) := by
  have h1 : g z = z.re • g 1 + z.im • g Complex.I := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    apply Complex.ext <;> simp
  have h2 : g (z * Complex.I) = z.re • g Complex.I + (-z.im) • g 1 := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    apply Complex.ext <;> simp
  have hc : ∀ (c : ℂ) (u : R), c ⊗ₜ[ℝ] u = c • ((1 : ℂ) ⊗ₜ[ℝ] u) := by
    intro c u
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, h2]
  simp only [TensorProduct.tmul_add, TensorProduct.tmul_smul]
  rw [hc (σ * Complex.I) (g 1), hc (σ * Complex.I) (g Complex.I)]
  simp only [← algebraMap_smul ℂ z.re, ← algebraMap_smul ℂ z.im, ← algebraMap_smul ℂ (-z.im)]
  match_scalars <;> simp only [Complex.coe_algebraMap, Complex.ofReal_neg] <;>
    first
    | ring1
    | linear_combination (z.im * σ * σ) * Complex.I_mul_I - z.im * hσ

private theorem idem_lemma_2 (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] :
    Nonempty (Idem ((A → ℝ) × (B → ℂ)) (A ⊕ (B × Bool))) := by
  let σ : Bool → ℂ := fun s => if s then 1 else -1
  have hσ : ∀ s, σ s * σ s = 1 := by
    intro s
    cases s <;> simp [σ]
  let g : B → ℂ →ₗ[ℝ] ((A → ℝ) × (B → ℂ)) := fun b =>
    (LinearMap.inr ℝ (A → ℝ) (B → ℂ)).comp (LinearMap.single ℝ (fun _ : B => ℂ) b)
  have hg : ∀ b w, g b w = ((0 : A → ℝ), Pi.single b w) := fun b w => rfl
  have hgmul : ∀ b u v, g b u * g b v = g b (u * v) := by
    intro b u v
    rw [hg, hg, hg]
    refine Prod.ext (by simp) (funext fun i => ?_)
    by_cases h : i = b
    · subst h
      simp
    · simp [h]
  have hgmul' : ∀ b b' u v, b ≠ b' → g b u * g b' v = 0 := by
    intro b b' u v hb
    rw [hg, hg]
    refine Prod.ext (by simp) (funext fun i => ?_)
    by_cases h : i = b
    · subst h
      simp [hb]
    · simp [h]
  have hc : ∀ (c : ℂ) (u : (A → ℝ) × (B → ℂ)), c ⊗ₜ[ℝ] u = c • ((1 : ℂ) ⊗ₜ[ℝ] u) := by
    intro c u
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  refine ⟨{
    e := Sum.elim (fun a => (1 : ℂ) ⊗ₜ[ℝ] ((Pi.single a 1, 0) : (A → ℝ) × (B → ℂ)))
      (fun p => (1 / 2 : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] g p.1 1 + (σ p.2 * Complex.I) ⊗ₜ[ℝ] g p.1 Complex.I))
    ch := Sum.elim
      (fun a => (algebraMap ℝ ℂ).comp ((Pi.evalRingHom (fun _ : A => ℝ) a).comp (RingHom.fst _ _)))
      (fun p => if p.2 then (starRingEnd ℂ).comp ((Pi.evalRingHom (fun _ : B => ℂ) p.1).comp (RingHom.snd _ _))
        else (Pi.evalRingHom (fun _ : B => ℂ) p.1).comp (RingHom.snd _ _))
    mul_e := ?_
    orth := ?_
    sum := ?_ }⟩
  · rintro (a | ⟨b, s⟩) x
    · simp only [Sum.elim_inl, RingHom.comp_apply]
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      have hx : x * ((Pi.single a 1, 0) : (A → ℝ) × (B → ℂ)) =
          x.1 a • ((Pi.single a (1 : ℝ), 0) : (A → ℝ) × (B → ℂ)) := by
        refine Prod.ext (funext fun i => ?_) (by simp)
        by_cases h : i = a
        · subst h
          simp
        · simp [h]
      rw [hx, TensorProduct.tmul_smul, algebraMap_smul]
      rfl
    · simp only [Sum.elim_inr]
      rw [mul_smul_comm, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
      simp only [one_mul]
      have hx : ∀ w : ℂ, x * g b w = g b (x.2 b * w) := by
        intro w
        rw [hg, hg]
        refine Prod.ext (by simp) (funext fun i => ?_)
        by_cases h : i = b
        · subst h
          simp
        · simp [h]
      rw [hx, hx, mul_one, one_tmul_add_tmul_mul_I_eq_smul_of_sq_eq_one (g b) (σ s) (x.2 b) (hσ s), smul_comm]
      congr 1
      cases s
      · simp [σ]
        all_goals (apply Complex.ext <;> simp)
      · simp [σ]
        all_goals (apply Complex.ext <;> simp)
  · rintro (a | ⟨b, s⟩) (a' | ⟨b', s'⟩) hne
    · have ha : a ≠ a' := fun h => hne (by rw [h])
      simp only [Sum.elim_inl]
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      have h0 : ((Pi.single a (1 : ℝ), 0) : (A → ℝ) × (B → ℂ)) * (Pi.single a' 1, 0) = 0 := by
        refine Prod.ext (funext fun i => ?_) (by simp)
        by_cases h : i = a
        · subst h
          simp [ha]
        · simp [h]
      rw [h0, TensorProduct.tmul_zero]
    · simp only [Sum.elim_inl, Sum.elim_inr]
      rw [mul_smul_comm, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
      have h0 : ∀ w, ((Pi.single a (1 : ℝ), 0) : (A → ℝ) × (B → ℂ)) * g b' w = 0 := by
        intro w
        rw [hg]
        exact Prod.ext (by simp) (by simp)
      rw [h0, h0]
      simp
    · simp only [Sum.elim_inl, Sum.elim_inr]
      rw [smul_mul_assoc, add_mul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
      have h0 : ∀ w, g b w * ((Pi.single a' (1 : ℝ), 0) : (A → ℝ) × (B → ℂ)) = 0 := by
        intro w
        rw [hg]
        exact Prod.ext (by simp) (by simp)
      rw [h0, h0]
      simp
    · simp only [Sum.elim_inr]
      rw [smul_mul_smul_comm]
      simp only [add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul]
      by_cases hb : b = b'
      · subst hb
        have hs : s ≠ s' := fun h => hne (by rw [h])
        have hc2 : ∀ (c d : ℂ) (u : (A → ℝ) × (B → ℂ)), (c * d) ⊗ₜ[ℝ] u = (c * d) • ((1 : ℂ) ⊗ₜ[ℝ] u) :=
          fun c d u => hc _ _
        simp only [hgmul, hc2]
        simp only [mul_one, one_mul, Complex.I_mul_I, map_neg, TensorProduct.tmul_neg]
        cases s <;> cases s' <;> simp only [ne_eq, not_true_eq_false, Bool.false_eq_true,
          not_false_eq_true, Bool.true_eq_false] at hs <;> simp only [σ, if_true, Bool.false_eq_true, if_false] <;>
          match_scalars <;>
          first
          | ring1
          | linear_combination (1 / 4 : ℂ) * Complex.I_mul_I
          | linear_combination (-1 / 4 : ℂ) * Complex.I_mul_I
      · simp only [hgmul' b b' _ _ hb, TensorProduct.tmul_zero, add_zero, smul_zero]
  · rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Fintype.sum_bool]
    have hb : ∀ b, (1 / 2 : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] g b 1 + (σ true * Complex.I) ⊗ₜ[ℝ] g b Complex.I) +
        (1 / 2 : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] g b 1 + (σ false * Complex.I) ⊗ₜ[ℝ] g b Complex.I) =
        (1 : ℂ) ⊗ₜ[ℝ] g b 1 := by
      intro b
      rw [hc (σ true * Complex.I), hc (σ false * Complex.I)]
      simp only [σ, if_true, Bool.false_eq_true, if_false]
      module
    simp only [hb]
    rw [← TensorProduct.tmul_sum, ← TensorProduct.tmul_sum, ← TensorProduct.tmul_add,
      Algebra.TensorProduct.one_def]
    congr 1
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [hg, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [hg, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]

theorem UpperTheory.exists_idempotent_decomposition_mixedSpace :
    ∀ (K : Type) [Field K] [NumberField K], ∃ (ι : Type) (_ : Fintype ι), Nonempty (Idem (mixedSpace K) ι) := by
  intro K _ _
  classical
  exact ⟨_, inferInstance, idem_lemma_2 {w : InfinitePlace K // w.IsReal} {w : InfinitePlace K // w.IsComplex}⟩
