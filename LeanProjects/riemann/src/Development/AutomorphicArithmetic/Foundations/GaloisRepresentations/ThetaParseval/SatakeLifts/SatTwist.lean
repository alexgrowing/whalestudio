import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace UpperTheory.Gal.TP.Loc

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)}
  {c : (w.adicCompletion K)ˣ →* ℂˣ}

private theorem unram_apply (hc : IsUnram c) {x : (w.adicCompletion K)ˣ}
    (hx : Valued.v (x : w.adicCompletion K) = 1) : c x = 1 := by
  haveI : (Valued.v : Valuation (w.adicCompletion K) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion K))
    (Valued.v : Valuation (w.adicCompletion K) (WithZero (Multiplicative ℤ)))
  exact hc x (he.eq_one_iff_eq_one.2 hx)

private theorem unram_det (hc : IsUnram c) {n : ℕ} {g : GL (Fin n) (w.adicCompletion K)} (hg : g ∈ KGL w n) :
    c (Matrix.GeneralLinearGroup.det g) = 1 :=
  unram_apply hc (GlobalTheory.SphGal.isUnitAt_det_of_mem hg)

private theorem unram_unif (hc : IsUnram c) {a b : (w.adicCompletion K)ˣ} (ha : IsUnifV K w (a : w.adicCompletion K))
    (hb : IsUnifV K w (b : w.adicCompletion K)) : c a = c b := by
  have h : c (a * b⁻¹) = 1 := by
    refine unram_apply hc ?_
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, show Valued.v (a : w.adicCompletion K) = _ from ha,
      show Valued.v (b : w.adicCompletion K) = _ from hb]
    exact mul_inv_cancel₀ (by simp)
  rw [map_mul, map_inv] at h
  exact mul_inv_eq_one.1 h

end SlopeTestRemainingChoices

theorem satTwist : SatTwist := by
  intro K _ _ w n c V _ _ ρ hc ϖ₀ h₀ B h
  have hf : ∀ x, x ∈ fixed (twist ρ (detChar (Fin n) c)) (KGL w n) ↔ x ∈ fixed ρ (KGL w n) := fun x => by
    simp only [GlobalTheory.LGrp.mem_fixed]
    refine forall₂_congr fun g hg => ?_
    rw [twist_apply, detChar_apply, unram_det hc hg, Units.val_one, one_smul]
  refine ⟨?_, fun y hy h0 => ?_⟩
  · obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h.1
    exact (Submodule.ne_bot_iff _).2 ⟨x, (hf x).2 hx, h0⟩
  · have hx := h.2 y ((hf y).1 hy) h0
    refine ⟨h0, hy, by rw [Multiset.card_map, hx.2.2.1], fun ϖ hϖ j hj => ?_⟩
    rw [GlobalTheory.SphGal.satEig_map_mul, mul_smul, ← hx.2.2.2 ϖ hϖ j hj, heckeVec, heckeVec, smul_finsum]
    refine finsum_congr fun t => ?_
    by_cases ht : Tj ℂ n (Ov K w) ϖ j t.out = 0
    · simp [ht]
    obtain ⟨a, ha, b, hb, e⟩ := Set.mem_of_indicator_ne_zero ht
    have hϖ0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
    have e2 : Matrix.GeneralLinearGroup.det t.out =
        Matrix.GeneralLinearGroup.det a * Units.mk0 ϖ hϖ0 ^ j * Matrix.GeneralLinearGroup.det b := by
      apply Units.ext
      change t.out.val.det = a.val.det * _ * b.val.det
      rw [e, Matrix.det_mul, Matrix.det_mul, GlobalTheory.SphGal.det_diagJ ϖ hj]
      simp
    have e3 : c (Units.mk0 ϖ hϖ0) = c ϖ₀ := unram_unif hc hϖ h₀
    rw [twist_apply, detChar_apply, e2, map_mul, map_mul, unram_det hc ha, unram_det hc hb, map_pow, e3, one_mul,
      mul_one, smul_comm, Units.val_pow_eq_pow_val]

end UpperTheory.Gal.TP.Loc

end
