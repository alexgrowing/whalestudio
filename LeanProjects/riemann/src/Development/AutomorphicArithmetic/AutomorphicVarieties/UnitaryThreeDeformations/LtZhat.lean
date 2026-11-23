import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.V.UnitaryThreeInertia.lt_zhat :
    ∀ {D E E' : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [Group E] [Finite E] [Group E'] (I : Subgroup D) (φ : D),
      (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ →
      (∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧ d φ = Multiplicative.ofAdd 1) →
      ∀ (q : E →* E') (w' : D →* E') (e : E), IsLocallyConstant w' → (∀ s ∈ I, w' s = 1) → q e = w' φ →
      ∃ w : D →* E, IsLocallyConstant w ∧ (∀ s ∈ I, w s = 1) ∧ q.comp w = w' ∧ ∀ g, w g ∈ Subgroup.zpowers e := by
  intro D E E' _ _ _ _ _ _ I φ hcl hd q w' e hw' hw'I hqe
  obtain ⟨d, hdc, hdI, hdφ⟩ := hd (orderOf e) (orderOf_pos e)
  haveI : NeZero (orderOf e) := ⟨(orderOf_pos e).ne'⟩
  let w : D →* E :=
    { toFun := fun g => e ^ (Multiplicative.toAdd (d g)).val
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [map_mul, toAdd_mul, ZMod.val_add, pow_mod_orderOf, pow_add] }
  have hwapp : ∀ g, w g = e ^ (Multiplicative.toAdd (d g)).val := fun g => rfl
  have hwc : IsLocallyConstant w := hdc.comp fun x => e ^ (Multiplicative.toAdd x).val
  have hφ : w φ = e := by
    rw [hwapp, hdφ, toAdd_ofAdd, ZMod.val_one_eq_one_mod, pow_mod_orderOf, pow_one]
  have hwI : ∀ s ∈ I, w s = 1 := by
    intro s hs
    rw [hwapp, hdI s hs]
    simp
  refine ⟨w, hwc, hwI, ?_, fun g => by rw [hwapp]; exact Subgroup.npow_mem_zpowers e _⟩
  have hf : IsLocallyConstant fun x => (q (w x))⁻¹ * w' x :=
    IsLocallyConstant.comp₂ (hwc.comp q) hw' fun a b => a⁻¹ * b
  have hclosed : IsClosed ((q.comp w).eqLocus w' : Set D) := by
    have e1 : ((q.comp w).eqLocus w' : Set D) = (fun x => (q (w x))⁻¹ * w' x) ⁻¹' {1} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, inv_mul_eq_one]
      exact Iff.rfl
    rw [e1]
    exact (hf.isClopen_fiber 1).isClosed
  have hle : I ⊔ Subgroup.zpowers φ ≤ (q.comp w).eqLocus w' := by
    refine sup_le (fun s hs => ?_) (Subgroup.zpowers_le.2 ?_)
    · show q (w s) = w' s
      rw [hwI s hs, map_one, hw'I s hs]
    · show q (w φ) = w' φ
      rw [hφ, hqe]
  have htop : ⊤ ≤ (q.comp w).eqLocus w' := by
    rw [← hcl]
    exact Subgroup.topologicalClosure_minimal _ hle hclosed
  ext g
  exact htop (Subgroup.mem_top g)
