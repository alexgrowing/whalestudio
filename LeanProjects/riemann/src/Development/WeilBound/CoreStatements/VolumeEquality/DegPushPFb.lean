import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs

noncomputable section

namespace SheetDecomposition.PF

open MvPolynomial

theorem ker_baseChange {k B K σ Φ Φ' : Type} [Field k] [CommRing B] [Algebra k B] [Field Φ] [Field Φ']
    [Algebra (MvPolynomial K k) Φ] [IsFractionRing (MvPolynomial K k) Φ] (a : k →+* Φ)
    (ha : ∀ c, a c = algebraMap (MvPolynomial K k) Φ (C c)) (ν : MvPolynomial K B →+* Φ') (hν : Function.Injective ν)
    (L : Φ →+* Φ') (hL : ∀ r, L (algebraMap (MvPolynomial K k) Φ r) = ν (map (algebraMap k B) r))
    (ψ : MvPolynomial σ k →ₐ[k] B) :
    RingHom.ker (eval₂Hom L fun s => ν (C (ψ (X s)))) = (RingHom.ker ψ).map (map a) := by
  classical
  obtain ⟨Θ, hΘ⟩ : ∃ f : MvPolynomial σ Φ →+* Φ', f = eval₂Hom L fun s => ν (C (ψ (X s))) :=
    ⟨_, rfl⟩
  suffices main : RingHom.ker Θ = (RingHom.ker ψ).map (map a) by
    subst hΘ
    exact main
  have hΘC : ∀ f : Φ, Θ (C f) = L f := fun f => by rw [hΘ, eval₂Hom_C]
  have hΘX : ∀ s : σ, Θ (X s) = ν (C (ψ (X s))) := fun s => by rw [hΘ, eval₂Hom_X']
  obtain ⟨α, hα⟩ : ∃ f : MvPolynomial K (MvPolynomial σ k) →+* MvPolynomial σ Φ,
      f = eval₂Hom (map a) fun i => C (algebraMap (MvPolynomial K k) Φ (X i)) := ⟨_, rfl⟩
  have hαC : ∀ p : MvPolynomial σ k, α (C p) = map a p := fun p => by rw [hα, eval₂Hom_C]
  have hαX : ∀ i : K, α (X i) = C (algebraMap (MvPolynomial K k) Φ (X i)) := fun i => by
    rw [hα, eval₂Hom_X']
  have hΘa : ∀ p : MvPolynomial σ k, Θ (map a p) = ν (C (ψ p)) := by
    have h : Θ.comp (map a) =
        ν.comp ((C : B →+* MvPolynomial K B).comp (ψ : MvPolynomial σ k →+* B)) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, map_C, hΘC, ha, hL, RingHom.coe_coe, algHom_C]
      · intro s
        simp only [RingHom.comp_apply, map_X, hΘX, RingHom.coe_coe]
    intro p
    exact DFunLike.congr_fun h p
  have hΘα : ∀ Q, Θ (α Q) = ν (map (ψ : MvPolynomial σ k →+* B) Q) := by
    have h : Θ.comp α = ν.comp (map (ψ : MvPolynomial σ k →+* B)) := by
      apply MvPolynomial.ringHom_ext
      · intro p
        simp only [RingHom.comp_apply, hαC, hΘa, map_C, RingHom.coe_coe]
      · intro i
        simp only [RingHom.comp_apply, hαX, hΘC, hL, map_X]
    intro Q
    exact DFunLike.congr_fun h Q
  have hαmapC : ∀ p : MvPolynomial K k, α (map (C : k →+* MvPolynomial σ k) p) =
      C (algebraMap (MvPolynomial K k) Φ p) := by
    have h : α.comp (map (C : k →+* MvPolynomial σ k)) =
        (C : Φ →+* MvPolynomial σ Φ).comp (algebraMap (MvPolynomial K k) Φ) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, map_C, hαC, ha]
      · intro i
        simp only [RingHom.comp_apply, map_X, hαX]
    intro p
    exact DFunLike.congr_fun h p
  have hCmem : ∀ q : MvPolynomial K k, C (algebraMap (MvPolynomial K k) Φ q) ∈ α.range :=
    fun q => RingHom.mem_range.mpr ⟨_, hαmapC q⟩
  have hXmem : ∀ s : σ, (X s : MvPolynomial σ Φ) ∈ α.range := fun s =>
    RingHom.mem_range.mpr ⟨C (X s), by rw [hαC, map_X]⟩
  have hden : ∀ P : MvPolynomial σ Φ, ∃ q : MvPolynomial K k, q ≠ 0 ∧
      C (algebraMap (MvPolynomial K k) Φ q) * P ∈ α.range := by
    intro P
    refine MvPolynomial.induction_on (motive := fun P => ∃ q : MvPolynomial K k, q ≠ 0 ∧
      C (algebraMap (MvPolynomial K k) Φ q) * P ∈ α.range) P ?_ ?_ ?_
    · intro f
      try dsimp only
      obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial K k) f
      refine ⟨q, nonZeroDivisors.ne_zero hq, ?_⟩
      rw [← C_mul, mul_div_cancel₀ _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq)]
      exact hCmem p
    · intro P₁ P₂ h₁ h₂
      try dsimp only at h₁ h₂ ⊢
      obtain ⟨q₁, hq₁, h₁⟩ := h₁
      obtain ⟨q₂, hq₂, h₂⟩ := h₂
      refine ⟨q₁ * q₂, mul_ne_zero hq₁ hq₂, ?_⟩
      have e : C (algebraMap (MvPolynomial K k) Φ (q₁ * q₂)) * (P₁ + P₂) =
          C (algebraMap (MvPolynomial K k) Φ q₂) * (C (algebraMap (MvPolynomial K k) Φ q₁) * P₁) +
            C (algebraMap (MvPolynomial K k) Φ q₁) * (C (algebraMap (MvPolynomial K k) Φ q₂) * P₂) := by
        rw [map_mul, C_mul]
        ring
      rw [e]
      exact add_mem (mul_mem (hCmem q₂) h₁) (mul_mem (hCmem q₁) h₂)
    · intro P s h
      try dsimp only at h ⊢
      obtain ⟨q, hq, h⟩ := h
      refine ⟨q, hq, ?_⟩
      rw [← mul_assoc]
      exact mul_mem h (hXmem s)
  apply le_antisymm
  · intro P hP
    rw [RingHom.mem_ker] at hP
    obtain ⟨q, hq, hmem⟩ := hden P
    obtain ⟨Q, hQ⟩ := RingHom.mem_range.mp hmem
    have hQ0 : map (ψ : MvPolynomial σ k →+* B) Q = 0 := by
      apply hν
      rw [map_zero, ← hΘα, hQ, map_mul, hP, mul_zero]
    have hJ : α Q ∈ (RingHom.ker ψ).map (map a) := by
      rw [Q.as_sum, map_sum]
      refine Ideal.sum_mem _ fun v _ => ?_
      rw [monomial_eq, map_mul, hαC]
      refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
      rw [RingHom.mem_ker]
      have hv := congrArg (coeff v) hQ0
      rw [coeff_map, coeff_zero] at hv
      exact hv
    have hqne : algebraMap (MvPolynomial K k) Φ q ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hq)
    have hP' : P = C (algebraMap (MvPolynomial K k) Φ q)⁻¹ * α Q := by
      rw [hQ, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hqne, C_1, one_mul]
    rw [hP']
    exact Ideal.mul_mem_left _ _ hJ
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [RingHom.mem_ker] at hp
    rw [Ideal.mem_comap, RingHom.mem_ker, hΘa, hp, map_zero, map_zero]

end SheetDecomposition.PF
