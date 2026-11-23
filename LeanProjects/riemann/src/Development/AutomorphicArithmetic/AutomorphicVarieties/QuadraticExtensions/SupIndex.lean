import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem relIndex_sup_normal {Γ : Type} [Group Γ] (K D H : Subgroup Γ) [K.Normal] (hD : D ≤ H) :
    H.relIndex (K ⊔ D) = H.relIndex K := by
  classical
  unfold Subgroup.relIndex Subgroup.index
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.map' (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ D)) fun a b h => ?_) ⟨?_, ?_⟩)
  · rw [QuotientGroup.leftRel_apply] at h ⊢
    simpa [Subgroup.mem_subgroupOf] using h
  · refine Quotient.ind' fun a => Quotient.ind' fun b => ?_
    intro h
    simp only [Quotient.map'_mk''] at h
    rw [Quotient.eq''] at h ⊢
    rw [QuotientGroup.leftRel_apply] at h ⊢
    simpa [Subgroup.mem_subgroupOf] using h
  · refine Quotient.ind' fun y => ?_
    obtain ⟨k, hk, d, hd, hkd⟩ := Subgroup.mem_sup_of_normal_left.mp y.2
    refine ⟨Quotient.mk'' ⟨k, hk⟩, ?_⟩
    simp only [Quotient.map'_mk'']
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    have hy : (y : Γ) = k * d := hkd.symm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, hy, inv_mul_cancel_left]
    exact hD hd

theorem UpperTheory.V.Two.supIndex :
    ∀ (Γ : Type) [Group Γ] (K W D : Subgroup Γ) [K.Normal] [W.Normal], W.index ≠ 0 → (K ⊔ D).index ≠ 0 → ((W ⊓ K) ⊔ D).index ≠ 0 ∧ ((W ⊓ K) ⊔ D).index ≤ W.index * (K ⊔ D).index := by
  intro Γ _ K W D _ _ hW hKD
  have hLKD : (W ⊓ K) ⊔ D ≤ K ⊔ D := sup_le_sup_right inf_le_right D
  have hDL : D ≤ (W ⊓ K) ⊔ D := le_sup_right
  have hWKL : W ⊓ K ≤ (W ⊓ K) ⊔ D := le_sup_left
  have h1 : ((W ⊓ K) ⊔ D).index = ((W ⊓ K) ⊔ D).relIndex K * (K ⊔ D).index := by
    rw [← relIndex_sup_normal K D _ hDL, Subgroup.relIndex_mul_index hLKD]
  have h2 : ((W ⊓ K) ⊔ D).relIndex K ∣ W.index := by
    have h := Subgroup.relIndex_dvd_of_le_left K hWKL
    rw [Subgroup.inf_relIndex_right] at h
    exact h.trans (Subgroup.relIndex_dvd_index_of_normal W K)
  have h3 : ((W ⊓ K) ⊔ D).relIndex K ≠ 0 := fun h => hW (Nat.eq_zero_of_zero_dvd (h ▸ h2))
  have h4 : ((W ⊓ K) ⊔ D).relIndex K ≤ W.index := Nat.le_of_dvd (Nat.pos_of_ne_zero hW) h2
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact mul_ne_zero h3 hKD
  · rw [h1]
    exact Nat.mul_le_mul_right _ h4
