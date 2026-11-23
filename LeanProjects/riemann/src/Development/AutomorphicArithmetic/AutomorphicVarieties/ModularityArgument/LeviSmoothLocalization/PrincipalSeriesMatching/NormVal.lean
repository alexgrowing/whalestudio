import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealExponentAbsSmoothCharacterLocalField

noncomputable section

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GroundTheory.Global.SemiLocal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

private theorem equivV {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    (ValuativeRel.valuation (v.adicCompletion K)).IsEquiv
      (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))) := by
  haveI : (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact ValuativeRel.isEquiv _ _

private theorem le_of_lt_one {a : WithZero (Multiplicative ℤ)} (h : a < 1) : a ≤ WithZero.exp (-1 : ℤ) := by
  by_cases h0 : a = 0
  · simp [h0]
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega

private theorem v_unif {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((unif (v.adicCompletion K) : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨p, hp⟩ := v.valuedAdicCompletion_surjective K (WithZero.exp (-1 : ℤ))
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hs := Classical.epsilon_spec (p := fun p : (v.adicCompletion K)ˣ =>
      ValuativeRel.valuation (v.adicCompletion K) (p : v.adicCompletion K) < 1 ∧
      ∀ x : v.adicCompletion K, ValuativeRel.valuation (v.adicCompletion K) x < 1 →
        ValuativeRel.valuation (v.adicCompletion K) x ≤ ValuativeRel.valuation (v.adicCompletion K) (p : v.adicCompletion K))
    ⟨Units.mk0 p hp0, (equivV v).lt_one_iff_lt_one.2 (by rw [Units.val_mk0, hp]; exact hlt), fun x hx =>
      ((equivV v) _ _).2 (by rw [Units.val_mk0, hp]; exact le_of_lt_one ((equivV v).lt_one_iff_lt_one.1 hx))⟩
  refine le_antisymm (le_of_lt_one ((equivV v).lt_one_iff_lt_one.1 hs.1)) ?_
  rw [← hp]
  exact ((equivV v) _ _).1 (hs.2 p ((equivV v).lt_one_iff_lt_one.2 (by rw [hp]; exact hlt)))

private theorem absNorm_eq {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v) :
    Ideal.absNorm w.1.asIdeal = Ideal.absNorm v.asIdeal ^ fdeg w := by
  obtain ⟨w, hw⟩ := w
  exact Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal v.asIdeal v.isPrime v.ne_bot

private theorem v_nm {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v) (x : (w.1.adicCompletion L)ˣ) :
    Valued.v ((nm w x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = Valued.v (x : w.1.adicCompletion L) ^ fdeg w := by
  have hN := absNorm_eq v w
  obtain ⟨w, hw⟩ := w
  obtain rfl : v = w.under (𝓞 K) := HeightOneSpectrum.ext hw.over
  have h := GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) w x
  have hm := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := K)
    (GroundTheory.Global.IdeleGroup.finiteEmbedding w x)
  rw [h] at hm
  have hm' := congrArg Subtype.val hm
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding] at hm'
  exact GlobalTheory.NormValGen.valuation_eq_pow_of_norm_eq _ w _ x hm' _ hN

theorem normVal :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.NormVal := by
  intro K L _ _ _ _ _ v w μ
  have hu : ValuativeRel.valuation (v.adicCompletion K)
      ((nm w (unif (w.1.adicCompletion L)) * (unif (v.adicCompletion K) ^ fdeg w)⁻¹ : (v.adicCompletion K)ˣ) :
        v.adicCompletion K) = 1 := by
    rw [(equivV v).eq_one_iff_eq_one, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul,
      map_inv₀, map_pow, v_nm, v_unif, v_unif]
    exact mul_inv_cancel₀ (pow_ne_zero _ WithZero.exp_ne_zero)
  have hN := absNorm_eq v w
  refine ⟨fun hμ => ⟨fun x hx => hμ _ ?_, ?_⟩, fun hμ => ?_, ?_, hN⟩
  · rw [(equivV v).eq_one_iff_eq_one, v_nm, (equivV w.1).eq_one_iff_eq_one.1 hx, one_pow]
  · have h := hμ _ hu
    rwa [map_mul, map_inv, mul_inv_eq_one, map_pow] at h
  · have h := GlobalTheory.SmoothCharNorm.norm_eq_one_of_valuation_eq_one μ hμ _ hu
    rw [map_mul, map_inv, map_pow, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, norm_mul, norm_inv,
      norm_pow, mul_inv_eq_one₀ (pow_ne_zero _ (norm_ne_zero_iff.2 (Units.ne_zero _)))] at h
    exact h
  · refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0, pow_zero, Ideal.absNorm_eq_one_iff] at hN
    exact w.1.isPrime.ne_top hN

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
