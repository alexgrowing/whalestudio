import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

namespace USum

variable {n : ℕ} {ε : Fin n → Bool}

theorem inK_real_smul {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    inK ε ((t : ℂ) • X) := by
  obtain ⟨hG, hC⟩ := hX
  refine ⟨?_, ?_⟩
  · unfold inG at hG ⊢
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
    have ht : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
    rw [ht, ← smul_add, hG, smul_zero]
  · rw [Matrix.smul_mul, Matrix.mul_smul, hC]

def zM (a b : Fin n) (c : ℂ) : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b c - Matrix.single b a (star c)

theorem Jm_comm_zM {a b : Fin n} (hab : ε a = ε b) (c : ℂ) : Jm ε * zM a b c = zM a b c * Jm ε := by
  have hd : ∀ i j, (i = a ∧ j = b) ∨ (i = b ∧ j = a) →
      (if ε i then (1 : ℂ) else -1) = if ε j then 1 else -1 := by
    rintro i j (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [hab]
  unfold Jm
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hij : (i = a ∧ j = b) ∨ (i = b ∧ j = a)
  · rw [hd i j hij, mul_comm]
  · have hz : zM a b c i j = 0 := by
      unfold zM
      simp only [Matrix.sub_apply, Matrix.single_apply]
      push_neg at hij
      rw [if_neg, if_neg, sub_zero]
      · exact fun h => hij.2 h.1.symm h.2.symm
      · exact fun h => hij.1 h.1.symm h.2.symm
    rw [hz, mul_zero, zero_mul]

theorem inK_zM {a b : Fin n} (hab : ε a = ε b) (c : ℂ) : inK ε (zM a b c) := by
  have hH : (zM a b c)ᴴ = -zM a b c := by
    ext i j
    have e1 : (a = j ∧ b = i) ↔ (b = i ∧ a = j) := and_comm
    have e2 : (b = j ∧ a = i) ↔ (a = i ∧ b = j) := and_comm
    simp only [zM, Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.single_apply, e1, e2]
    split_ifs <;> simp
  refine ⟨?_, (Jm_comm_zM hab c).symm⟩
  unfold inG
  rw [hH, Jm_comm_zM hab c, neg_mul, neg_add_cancel]

section Act

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem actM_single (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (c : ℂ) :
    actM E (Matrix.single a b c) = c • E a b := by
  classical
  unfold actM
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp [Matrix.single_apply]
  · intro j _ hj
    simp [Matrix.single_apply, Ne.symm hj]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    simp [Matrix.single_apply, Ne.symm hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem actM_sub (E : Fin n → Fin n → Module.End ℂ M) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    actM E (X - Y) = actM E X - actM E Y := by
  unfold actM
  simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem actM_zM (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (c : ℂ) :
    actM E (zM a b c) = c • E a b - star c • E b a := by
  unfold zM
  rw [actM_sub, actM_single, actM_single]

end Act

section Rep

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}
  {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {E₂ : Fin n → Fin n → Module.End ℂ D₂}
  {V₁ : Submodule ℂ D₁} {V₂ : Submodule ℂ D₂}

private theorem exp_smul_mem_Kset_of_skew_of_commute_Jm {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε := by
  obtain ⟨hG, hC⟩ := hX
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hskew : Xᴴ = -X := by
    have h1 : Xᴴ * Jm ε = -(X * Jm ε) := by
      rw [hC]
      exact eq_neg_of_add_eq_zero_left hG
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = -(X * Jm ε) * Jm ε := by rw [h1]
      _ = -X := by rw [Matrix.neg_mul, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have ht : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
  have hY : ((t : ℂ) • X)ᴴ = -((t : ℂ) • X) := by
    rw [Matrix.conjTranspose_smul, hskew, ht, smul_neg]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hY,
      ← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl ((t : ℂ) • X))), add_neg_cancel,
      NormedSpace.exp_zero]
  · letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    have hc : Commute ((t : ℂ) • X) (Jm ε) := by
      show (t : ℂ) • X * Jm ε = Jm ε * ((t : ℂ) • X)
      rw [Matrix.smul_mul, Matrix.mul_smul, hC]
    exact hc.exp_left.eq

theorem phi_actM_inK (hD₁ : IsDerivedOn ε σ₁ D₁ E₁) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂)
    [FiniteDimensional ℂ V₁]
    (hVK₁ : ∀ k ∈ Kset ε, ∀ v ∈ V₁, ∃ w ∈ V₁, (w : H₁) = σ₁ k v) (φ : V₁ →ₗ[ℂ] V₂)
    (hφK : ∀ k ∈ Kset ε, ∀ (v : V₁) (w : V₁), ((w : D₁) : H₁) = σ₁ k ((v : D₁) : H₁) →
      (((φ w : V₂) : D₂) : H₂) = σ₂ k (((φ v : V₂) : D₂) : H₂))
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (v u : V₁) (hu : (u : D₁) = actM E₁ X v) :
    ((actM E₂ X ((φ v : V₂) : D₂) : D₂) : H₂) = (((φ u : V₂) : D₂) : H₂) := by
  classical
  have hk : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε := fun t => exp_smul_mem_Kset_of_skew_of_commute_Jm hX t
  choose w hwV hw using fun t : ℝ => hVK₁ _ (hk t) (v : D₁) v.2
  let W : ℝ → V₁ := fun t => ⟨w t, hwV t⟩
  have hW : ∀ t, (((W t : V₁) : D₁) : H₁) = σ₁ (NormedSpace.exp ((t : ℂ) • X)) ((v : D₁) : H₁) := hw
  have h1 : HasDerivAt (fun t : ℝ => (((W t : V₁) : D₁) : H₁)) (((u : V₁) : D₁) : H₁) 0 := by
    have hd := hD₁.deriv X hX.1 (v : D₁)
    rw [← hu] at hd
    exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hW t)
  have h2 : HasDerivAt W u 0 := by
    rw [hasDerivAt_iff_isLittleO_nhds_zero] at h1 ⊢
    rw [← Asymptotics.isLittleO_norm_left] at h1 ⊢
    exact h1.congr_left (fun h => rfl)
  let L : V₁ →L[ℂ] H₂ := LinearMap.toContinuousLinearMap ((D₂.subtype.comp V₂.subtype).comp φ)
  have h3 : HasDerivAt (fun t => L (W t)) (L u) 0 :=
    (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  have h4 : (fun t => L (W t)) =
      fun t : ℝ => σ₂ (NormedSpace.exp ((t : ℂ) • X)) (((φ v : V₂) : D₂) : H₂) := by
    funext t
    exact hφK _ (hk t) v (W t) (hW t)
  rw [h4] at h3
  exact (hD₂.deriv X hX.1 ((φ v : V₂) : D₂)).unique h3

private theorem eq_half_smul_sub_I_smul_combo {M : Type*} [AddCommGroup M] [Module ℂ M] (A B : M) :
    A = (1 / 2 : ℂ) • ((A - B) - Complex.I • (Complex.I • A - (-Complex.I) • B)) := by
  rw [smul_sub Complex.I, smul_smul, smul_smul, Complex.I_mul_I, mul_neg, Complex.I_mul_I, neg_neg,
    neg_one_smul, one_smul]
  rw [show (A - B) - (-A - B) = (2 : ℂ) • A by module, smul_smul]
  norm_num

theorem phi_E_comm (hD₁ : IsDerivedOn ε σ₁ D₁ E₁) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂)
    [FiniteDimensional ℂ V₁] (hst : IsKStableSub ε E₁ V₁)
    (hVK₁ : ∀ k ∈ Kset ε, ∀ v ∈ V₁, ∃ w ∈ V₁, (w : H₁) = σ₁ k v) (φ : V₁ →ₗ[ℂ] V₂)
    (hφK : ∀ k ∈ Kset ε, ∀ (v : V₁) (w : V₁), ((w : D₁) : H₁) = σ₁ k ((v : D₁) : H₁) →
      (((φ w : V₂) : D₂) : H₂) = σ₂ k (((φ v : V₂) : D₂) : H₂))
    {a b : Fin n} (hab : ε a = ε b) (v : V₁) :
    E₂ a b ((φ v : V₂) : D₂) = ((φ ⟨E₁ a b v, hst a b hab _ v.2⟩ : V₂) : D₂) := by
  have hmem : ∀ c : ℂ, c • E₁ a b (v : D₁) - star c • E₁ b a (v : D₁) ∈ V₁ := fun c =>
    V₁.sub_mem (V₁.smul_mem _ (hst a b hab _ v.2)) (V₁.smul_mem _ (hst b a hab.symm _ v.2))
  let wc : ℂ → V₁ := fun c => ⟨c • E₁ a b (v : D₁) - star c • E₁ b a (v : D₁), hmem c⟩
  have key : ∀ c : ℂ, c • E₂ a b ((φ v : V₂) : D₂) - star c • E₂ b a ((φ v : V₂) : D₂) =
      ((φ (wc c) : V₂) : D₂) := by
    intro c
    have h := phi_actM_inK hD₁ hD₂ hVK₁ φ hφK (inK_zM hab c) v (wc c) (by rw [actM_zM]; rfl)
    rw [actM_zM, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply] at h
    exact Subtype.ext h
  have hw0 : (⟨E₁ a b v, hst a b hab _ v.2⟩ : V₁) = (1 / 2 : ℂ) • (wc 1 - Complex.I • wc Complex.I) := by
    apply Subtype.ext
    show E₁ a b (v : D₁) = (1 / 2 : ℂ) • (((1 : ℂ) • E₁ a b (v : D₁) - star (1 : ℂ) • E₁ b a (v : D₁)) -
      Complex.I • (Complex.I • E₁ a b (v : D₁) - star Complex.I • E₁ b a (v : D₁)))
    rw [star_one, one_smul, one_smul, Complex.star_def, Complex.conj_I]
    exact eq_half_smul_sub_I_smul_combo _ _
  rw [hw0, map_smul, map_sub, map_smul]
  show E₂ a b ((φ v : V₂) : D₂) =
    (1 / 2 : ℂ) • (((φ (wc 1) : V₂) : D₂) - Complex.I • ((φ (wc Complex.I) : V₂) : D₂))
  rw [← key 1, ← key Complex.I, star_one, one_smul, one_smul, Complex.star_def, Complex.conj_I]
  exact eq_half_smul_sub_I_smul_combo _ _

end Rep

end USum

end ReciprocityTheory.ChartRestriction.DS
