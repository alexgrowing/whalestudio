import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.PhEvenOf
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.IdealLatticeHolds

namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

theorem lamOf_lat_holds (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 ∧ lamOf D cc δ = lat2 w₁ w₂ :=
  lamOf_lat idealLattice_holds D cc hc δ hδ

theorem delta_ne_holds (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 :=
  delta_ne' idealLattice_holds D cc hc δ hδ

theorem sgStar_spec (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    Differentiable ℂ (sgStar (lamOf D cc δ)) ∧ deriv (sgStar (lamOf D cc δ)) 0 = 1 ∧
      (∀ z, sgStar (lamOf D cc δ) (-z) = -sgStar (lamOf D cc δ) z) := by
  obtain ⟨w₁, w₂, hw, hL⟩ := lamOf_lat_holds D cc hc δ (delta_ne_holds D cc hc δ hδ)
  have h := sigmaStarEx_holds w₁ w₂ hw
  rw [hL]
  unfold sgStar
  have hs := Classical.epsilon_spec h
  exact ⟨hs.1, hs.2.1, hs.2.2.1⟩

theorem area_lamOf (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ) (hδ : δ ≠ 0) :
    area (lamOf D cc δ) = ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * Real.sqrt |(NumberField.discr D.host.K : ℝ)| / 2 := by
  have h := idealLattice_holds D.host.K (D.host.φ₀.comp (algebraMap D.host.K D.host.E))
    (Formalism.MainNotions.Ext.finrank_K D.host) (Formalism.MainNotions.Ext.no_real_K D.host) cc δ hc hδ
  exact h.2

end Formalism.MainNotions.Ext
