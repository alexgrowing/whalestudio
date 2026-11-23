import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.CharacteristicFunctionIntegralInvariant

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel NNReal

namespace Ad3.SchwartzSpaceL2.UnramifiedWhittakerGL2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in
theorem ord_unif_zpow (n : ℤ) : ord ((GLnLocal.uniformizer F : F) ^ n) = n := by
  rw [← Iwasawa.coe_uniformizerUnit, ← Units.val_zpow_eq_zpow_val, ord_units_zpow,
    Iwasawa.coe_uniformizerUnit, ord_uniformizer (GLnLocal.irreducible_uniformizer F), mul_one]

omit [MeasurableSpace F] [BorelSpace F] in
theorem unif_zpow_ne_zero (n : ℤ) : (GLnLocal.uniformizer F : F) ^ n ≠ 0 := by
  rw [← Iwasawa.coe_uniformizerUnit, ← Units.val_zpow_eq_zpow_val]
  exact Units.ne_zero _

omit [MeasurableSpace F] [BorelSpace F] in
theorem ord_det {u k : GL (Fin 2) F} (hu : u ∈ Iwasawa.unipotent F 2)
    (hk : k ∈ GLnLocal.integralGL F 2) (l : Fin 2 → ℤ) :
    ord ((GeneralLinearGroup.det (u * Iwasawa.torusPow F 2 l * k) : Fˣ) : F) = l 0 + l 1 := by
  obtain ⟨h00, h11, h10⟩ := unip_entries hu
  have hdu : GeneralLinearGroup.det u = 1 := by
    ext
    rw [GeneralLinearGroup.val_det_apply, det_fin_two, h00, h11, h10]
    simp
  have hdt : ((GeneralLinearGroup.det (Iwasawa.torusPow F 2 l) : Fˣ) : F) =
      (GLnLocal.uniformizer F : F) ^ (l 0) * (GLnLocal.uniformizer F : F) ^ (l 1) := by
    rw [GeneralLinearGroup.val_det_apply, Iwasawa.coe_torusPow, det_diagonal, Fin.prod_univ_two]
  rw [map_mul, map_mul, hdu, one_mul, Units.val_mul, hdt,
    ord_mul (mul_ne_zero (unif_zpow_ne_zero _) (unif_zpow_ne_zero _)) (Units.ne_zero _),
    ord_mul (unif_zpow_ne_zero _) (unif_zpow_ne_zero _), ord_unif_zpow, ord_unif_zpow,
    GodementSectionLocal.ord_det_eq_zero hk, add_zero]

omit [MeasurableSpace F] [BorelSpace F] in
theorem indicator_integers_eq {y : F} (hy : y ≠ 0) :
    (𝒪[F] : Set F).indicator (1 : F → ℂ) y = if 0 ≤ ord y then 1 else 0 := by
  have : y ∈ (𝒪[F] : Set F) ↔ 0 ≤ ord y := by
    rw [SetLike.mem_coe, ← mem_valBall_zero_iff, mem_valBall_iff_le_ord hy]
  by_cases h : 0 ≤ ord y
  · rw [Set.indicator_of_mem (this.2 h), if_pos h]; rfl
  · rw [Set.indicator_of_notMem (fun h' => h (this.1 h')), if_neg h]

theorem W_formula (ψ : AddChar F Circle) (hψ : IsStd ψ) (μ₁ μ₂ : Fˣ →* ℂˣ)
    (hr₁ : IsUnramifiedChar μ₁) (hr₂ : IsUnramifiedChar μ₂) {u k : GL (Fin 2) F}
    (hu : u ∈ Iwasawa.unipotent F 2) (hk : k ∈ GLnLocal.integralGL F 2) (l : Fin 2 → ℤ) :
    W2 ψ μ₁ μ₂ (phi0 F) (u * Iwasawa.torusPow F 2 l * k) =
      ((μ₂ (unifUnit F) : ℂˣ) : ℂ) ^ (l 0 + l 1) *
        ((((residueCard F : ℝ≥0) ^ (-(l 0 + l 1)) : ℝ≥0) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
        ((ψ ((u : Matrix (Fin 2) (Fin 2) F) 0 1) : ℂ) * (residueCard F : ℂ) ^ (l 1) *
          ∑ j ∈ Finset.Icc (-l 0) (-l 1),
            ((((μ₁ (unifUnit F))⁻¹ * μ₂ (unifUnit F) : ℂˣ) : ℂ)) ^ j) := by
  have hdet := ord_det hu hk l
  set χ0 : ℂˣ := (μ₁ (unifUnit F))⁻¹ * μ₂ (unifUnit F) with hχ0
  set q : ℂ := (residueCard F : ℂ) with hq
  have hq0 : q ≠ 0 := residueCard_ne_zero_complex
  set C : ℂ := (ψ ((u : Matrix (Fin 2) (Fin 2) F) 0 1) : ℂ) * q ^ (l 1) with hC
  have hpt : ∀ h : Fˣ,
      (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
        (∫ x, phi0 F (![(h : F), h * x] ᵥ*
          ((u * Iwasawa.torusPow F 2 l * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
          (ψ (-x) : ℂ) ∂selfDualMeasure ψ) =
      ∑ j ∈ Finset.Icc (-l 0) (-l 1), (ordShell F j).indicator (fun _ => C * (χ0 : ℂ) ^ j) h := by
    classical
    intro h
    have hb0 : (h : F) * (GLnLocal.uniformizer F : F) ^ (l 1) ≠ 0 :=
      mul_ne_zero h.ne_zero (unif_zpow_ne_zero _)
    have ha0 : (h : F) * (GLnLocal.uniformizer F : F) ^ (l 0) ≠ 0 :=
      mul_ne_zero h.ne_zero (unif_zpow_ne_zero _)
    have hin : (∫ x, phi0 F (![(h : F), h * x] ᵥ*
          ((u * Iwasawa.torusPow F 2 l * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
          (ψ (-x) : ℂ) ∂selfDualMeasure ψ) =
        (𝒪[F] : Set F).indicator 1 ((h : F) * (GLnLocal.uniformizer F : F) ^ (l 0)) *
          ((ψ ((u : Matrix (Fin 2) (Fin 2) F) 0 1) : ℂ) * (if ord ((h : F) * (GLnLocal.uniformizer F : F) ^ (l 1)) ≤ 0 then
            q ^ (ord ((h : F) * (GLnLocal.uniformizer F : F) ^ (l 1))) else 0)) := by
      simp_rw [vec_eq hu hk l]
      rw [← inner_eq ψ hψ _ _ hb0, ← integral_const_mul]
      congr 1
      funext x
      ring
    rw [hin, indicator_integers_eq ha0, ord_mul h.ne_zero (unif_zpow_ne_zero _),
      ord_mul h.ne_zero (unif_zpow_ne_zero _), ord_unif_zpow, ord_unif_zpow]
    have hmu : (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) = (χ0 : ℂ) ^ ord (h : F) := by
      rw [quasiChar_apply_of_isUnramified hr₁ h, quasiChar_apply_of_isUnramified hr₂ h, hχ0,
        ← _root_.inv_zpow, ← mul_zpow, Units.val_zpow_eq_zpow_val]
    have hmp : mp h 1 = q ^ (-ord (h : F)) := by
      rw [mp, Complex.cpow_one, modulus_of_ne_zero h.ne_zero, hq]
      push_cast
      rfl
    rw [hmu, hmp]
    simp only [Set.indicator_apply, mem_ordShell]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_Icc]
    set o := ord (h : F)
    by_cases h1 : 0 ≤ o + l 0 <;> by_cases h2 : o + l 1 ≤ 0
    · rw [if_pos h1, if_pos h2, if_pos ⟨by omega, by omega⟩, hC, zpow_add₀ hq0, _root_.zpow_neg]
      field_simp
    · rw [if_neg h2, if_neg (show ¬(-l 0 ≤ o ∧ o ≤ -l 1) by omega)]; simp
    · rw [if_neg h1, if_neg (show ¬(-l 0 ≤ o ∧ o ≤ -l 1) by omega)]; simp
    · rw [if_neg h1, if_neg (show ¬(-l 0 ≤ o ∧ o ≤ -l 1) by omega)]; simp
  unfold W2
  rw [quasiChar_apply_of_isUnramified hr₂, hdet]
  congr 1
  · rw [mp, modulus_of_ne_zero (Units.ne_zero _), hdet, Units.val_zpow_eq_zpow_val]
  · refine (integral_congr_ae (Filter.Eventually.of_forall hpt)).trans ?_
    have hint : ∀ j : ℤ, Integrable ((ordShell F j).indicator (fun _ : Fˣ => C * (χ0 : ℂ) ^ j))
        (multHaar F) := fun j =>
      (integrableOn_const (by rw [multHaar_ordShell]; exact ENNReal.one_ne_top)).integrable_indicator
        (measurableSet_ordShell j)
    rw [integral_finset_sum _ (fun j _ => hint j), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_indicator_const _ (measurableSet_ordShell j), measureReal_def, multHaar_ordShell,
      ENNReal.toReal_one, one_smul]

end Ad3.SchwartzSpaceL2.UnramifiedWhittakerGL2
