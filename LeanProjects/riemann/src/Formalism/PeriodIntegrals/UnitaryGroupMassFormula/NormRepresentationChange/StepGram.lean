import Mathlib
import Formalism.PeriodIntegrals.PairValDefs
import Formalism.PeriodIntegrals.NormRepChange
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Development

noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.PairValDefs Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepGram (D : D7) : StepGram D := by
  intro T T' G G₁ G₂ n m N M hn hN hM hG
  unfold ZhatL Zhat brS frame at *
  have hiso : ∀ x y, (VS D).hT (n x) (n y) = (VS D).hT x y := hn
  funext a b

  have hL : ∑ c, star (N c a) * (VS D).hT (G.fl.fvec c) (G₂.fl.fvec b) =
      (VS D).hT (n (G.fl.fvec a)) (G₂.fl.fvec b) := by
    rw [hN a]
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, starRingEnd_apply]
  have hR : ∑ c, (VS D).hT (G.fl.fvec a) (G₁.fl.fvec c) * M c b =
      (VS D).hT (G.fl.fvec a) (m (G₁.fl.fvec b)) := by
    rw [hM b]
    simp only [map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  change ∑ c, star (N c a) * (VS D).hT (G.fl.fvec c) (G₂.fl.fvec b) =
    ∑ c, (VS D).hT (G.fl.fvec a) (G₁.fl.fvec c) * M c b
  rw [hL, hR, hG b, hiso]

end PI.NRCW
