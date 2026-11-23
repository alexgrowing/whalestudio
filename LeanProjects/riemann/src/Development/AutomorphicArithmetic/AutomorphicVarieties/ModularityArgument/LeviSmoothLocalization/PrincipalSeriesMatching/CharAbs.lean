import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterAbsoluteValuePower
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem isUnifAt_unif {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    Formalism.L2.Host.IsUnifAt v (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif (v.adicCompletion K)) := by
  have hiff : ∀ x y : v.adicCompletion K,
      ValuativeRel.valuation (v.adicCompletion K) x ≤ ValuativeRel.valuation (v.adicCompletion K) y ↔
        Valued.v x ≤ Valued.v y := by
    intro x y
    letI : (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    exact ValuativeRel.isEquiv _ _ x y
  have hlt1 : ∀ x : v.adicCompletion K,
      ValuativeRel.valuation (v.adicCompletion K) x < 1 ↔ Valued.v x < 1 := by
    intro x
    have h := hiff 1 x
    rw [map_one, map_one] at h
    rw [lt_iff_not_ge, lt_iff_not_ge, h]
  have hdisc : ∀ a : WithZero (Multiplicative ℤ), a < 1 → a ≤ WithZero.exp (-1) := by
    intro a h
    rcases eq_or_ne a 0 with rfl | ha
    · exact zero_le'
    · rw [← WithZero.exp_log ha] at h ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
      rw [WithZero.exp_le_exp]
      omega
  have hexp : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hπ : Valued.v ((Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v) : (v.adicCompletion K)ˣ) :
      v.adicCompletion K) = WithZero.exp (-1) := Formalism.L2.Host.unif_spec v
  have hex : ∃ p : (v.adicCompletion K)ˣ,
      ValuativeRel.valuation (v.adicCompletion K) (p : v.adicCompletion K) < 1 ∧
        ∀ x : v.adicCompletion K, ValuativeRel.valuation (v.adicCompletion K) x < 1 →
          ValuativeRel.valuation (v.adicCompletion K) x ≤
            ValuativeRel.valuation (v.adicCompletion K) (p : v.adicCompletion K) := by
    refine ⟨Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v), ?_, ?_⟩
    · rw [hlt1, hπ]
      exact hexp
    · intro x hx
      rw [hiff, hπ]
      exact hdisc _ ((hlt1 x).1 hx)
  obtain ⟨hu1, hu2⟩ := Classical.epsilon_spec hex
  unfold Formalism.L2.Host.IsUnifAt UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif
  apply le_antisymm
  · exact hdisc _ ((hlt1 _).1 hu1)
  · rw [← hπ, ← hiff]
    apply hu2
    rw [hlt1, hπ]
    exact hexp

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.charAbs :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.CharAbs := by
  intro K _ _ χ
  refine ⟨-(GlobalTheory.HeckeNormPow.toQC χ).exponent, fun v => ⟨GlobalTheory.HeckeComp.smooth_loc χ v, ?_⟩⟩
  have h1 := (GlobalTheory.HeckeNormPow.toQC χ).norm_apply
    (GroundTheory.Global.IdeleClassGroup.mk K (GroundTheory.Global.IdeleGroup.finiteEmbedding v
      (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif (v.adicCompletion K))))
  rw [GroundTheory.Global.IdeleClassGroup.ideleModule_mk,
    GroundTheory.Global.ideleModule_finiteEmbedding_of_uniformizer (isUnifAt_unif v),
    Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)] at h1
  exact h1
