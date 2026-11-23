import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Imports
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem liePowerSum_isHomogeneous (d : IndexData) (m : ℕ) (e : Emb d) :
    (liePowerSum d m e).IsHomogeneous m := by
  unfold liePowerSum lowerPowerSum
  split_ifs
  · refine IsHomogeneous.sum _ _ _ fun i _ => ?_
    simpa using (isHomogeneous_X ℚ (e.1, i)).neg.pow m
  · refine IsHomogeneous.sum _ _ _ fun i _ => ?_
    simpa using (isHomogeneous_X ℚ (e.1, i)).pow m

theorem RestPWellDefined.proof : RestPWellDefined.Statement := by
  intro d vol p φ F Q Q' hQ hQ'
  unfold rest₂
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk2, hkN⟩ := Finset.mem_Icc.mp hk
  congr 1
  funext n
  unfold restSeries
  have hG := liePowerSum_isHomogeneous d (k - 1) ((φ ^ (n + 1)) (τ, false))
  have h := RestTerms.RestTermWellDefined.full d.f d.N F Q Q' hQ hQ' k (by omega) hkN τ _ hG
  unfold RestTerms.restTerm at h
  have e : ∀ R : ℕ → Fin d.f → XPoly d,
      (k : ℚ) * intFl d (liePowerSum d (k - 1) ((φ ^ (n + 1)) (τ, false)) * R k τ) =
        flagNormalisation d.f d.N *
          ((k : ℚ) * RestTerms.flagIntegral d.f d.N (liePowerSum d (k - 1) ((φ ^ (n + 1)) (τ, false)) * R k τ)) := by
    intro R
    simp only [intFl, LinearMap.smul_apply, flagIntegralLin, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    ring
  rw [e Q, e Q', h]

theorem RestPWellDefined.full : RestPWellDefined.Statement := RestPWellDefined.proof

end GroundTheory.Heights₂.Heights.TheoremB
