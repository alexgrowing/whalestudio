import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CornerUnits

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.frobenius_corner_units :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Type) [CommRing K] [Algebra C K] (ρ : NRep F 3 K), Cone O C ρ → CornerUnits ρ := by
  intro l _ O _ _ _ _ F C₀ hF C _ _ _ K _ _ ρ hC v
  obtain ⟨g, hg⟩ := hF.f3 v
  obtain ⟨χ, hχ, hχρ⟩ := hC.psi
  have key : ∀ a : C, res O C a ≠ 0 → IsUnit (algebraMap C K a) := by
    intro a ha
    apply IsUnit.map
    by_contra hu
    exact ha ((res_eq_zero_iff O C a).mpr ((IsLocalRing.mem_maximalIdeal a).mpr (mem_nonunits_iff.mpr hu)))
  have w0 : w 3 0 = 1 := by simp [w]
  have w1 : w 3 1 = 0 := by simp [w]
  have w2 : w 3 2 = -1 := by simp [w]
  have hg' : F.Ψ ((F.loc0 v g : F.del.ker) : F.Γ) ^ 2 ≠ 1 := hg
  have hu1 : ((F.Ψ ((F.loc0 v g : F.del.ker) : F.Γ) : (ResidueField O)ˣ) : ResidueField O) ≠ 1 := by
    intro h
    apply hg'
    ext
    rw [Units.val_pow_eq_pow_val, h, one_pow, Units.val_one]
  have hu2 : (((F.Ψ ((F.loc0 v g : F.del.ker) : F.Γ))⁻¹ : (ResidueField O)ˣ) : ResidueField O) ≠ 1 := by
    intro h
    apply hg'
    have h1 : F.Ψ ((F.loc0 v g : F.del.ker) : F.Γ) = 1 := inv_eq_one.mp (Units.ext (by rw [h, Units.val_one]))
    rw [h1, one_pow]
  obtain ⟨c0, hc0, hr0⟩ := hC.dg (F.loc0 v g) 0
  obtain ⟨c1, hc1, hr1⟩ := hC.dg (F.loc0 v g) 1
  obtain ⟨c2, hc2, hr2⟩ := hC.dg (F.loc0 v g) 2
  rw [w0, zpow_one] at hr0
  rw [w1, zpow_zero, Units.val_one] at hr1
  rw [w2, _root_.zpow_neg_one] at hr2
  have x0 : res O C (χ v 0 g) = ((F.Ψ ((F.loc0 v g : F.del.ker) : F.Γ) : (ResidueField O)ˣ) : ResidueField O) := by
    have h := (hχ v 0).2 g
    rw [w0, zpow_one] at h
    exact h
  have x1 : res O C (χ v 1 g) = 1 := by
    have h := (hχ v 1).2 g
    rw [w1, zpow_zero, Units.val_one] at h
    exact h
  have x2 : res O C (χ v 2 g) = (((F.Ψ ((F.loc0 v g : F.del.ker) : F.Γ))⁻¹ : (ResidueField O)ˣ) : ResidueField O) := by
    have h := (hχ v 2).2 g
    rw [w2, _root_.zpow_neg_one] at h
    exact h
  have h02 : ((0 : Fin 3) : Fin 3) ≠ 2 := by decide
  obtain ⟨m, hm, hme⟩ := hC.cyc [(F.loc0 v g, 0, 2), (F.loc0 v g, 2, 0)] (by simp [w])
    ⟨(F.loc0 v g, 0, 2), by simp, h02⟩
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hme
  refine ⟨g, ?_, ?_, ?_⟩
  · have hk := key (c1 - χ v 0 g) ?_
    · rwa [map_sub, hc1, hχρ] at hk
    · rw [map_sub, hr1, x0]
      exact sub_ne_zero.mpr (Ne.symm hu1)
  · have hk := key (c1 - χ v 2 g) ?_
    · rwa [map_sub, hc1, hχρ] at hk
    · rw [map_sub, hr1, x2]
      exact sub_ne_zero.mpr (Ne.symm hu2)
  · have hk := key ((c0 - χ v 1 g) * (c2 - χ v 1 g) - m) ?_
    · rwa [map_sub, map_mul, map_sub, map_sub, hc0, hc2, hχρ, hme] at hk
    · rw [map_sub, map_mul, map_sub, map_sub, hr0, hr2, x1, (res_eq_zero_iff O C m).mpr hm, sub_zero]
      exact mul_ne_zero (sub_ne_zero.mpr hu1) (sub_ne_zero.mpr hu2)
