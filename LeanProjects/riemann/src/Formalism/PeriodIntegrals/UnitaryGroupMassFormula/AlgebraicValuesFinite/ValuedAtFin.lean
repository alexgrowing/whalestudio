import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.ClassSame

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace PI.AlgValsFin.W

variable {L : Type} [Field L] [NumberField L]

theorem valued_atFin (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    Valued.v ((atFin v k : (v.adicCompletion L)ˣ) : v.adicCompletion L) = WithZero.exp (-ordF v k) := by
  unfold ordF
  rw [neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).2 k.ne_zero)]
  simp only [atFin, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  first
  | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : L)
  | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation v (k : L)
  | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := L) v (k : L)
  | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := L) v (k : L)
  | exact Valued.extension_extends _
  | rfl
  | simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  | simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation]

theorem locVal : LocVal L := by
  intro χ v k hχ
  have hu : IsUnifAt v (atFin v (unif v)) := Classical.choose_spec (exists_unif v)
  unfold IsUnifAt at hu
  have hunit : IsUnitAt v (atFin v k * (atFin v (unif v) ^ ordF v k)⁻¹) := by
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀, hu,
      valued_atFin, ← WithZero.exp_zsmul, smul_neg, smul_eq_mul, mul_one,
      mul_inv_cancel₀ WithZero.exp_ne_zero]
  have h1 := hχ _ hunit
  rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h1
  rw [h1]
  rfl

end PI.AlgValsFin.W
