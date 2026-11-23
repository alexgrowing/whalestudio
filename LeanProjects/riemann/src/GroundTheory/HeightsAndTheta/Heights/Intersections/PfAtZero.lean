import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem pfAt_zero (hAI3 : PushforwardArithIntersection.Statement) (I : AllFam) (hI : I.IsFamily) : PFAt I 0 := by
  intro K _ ι _ K' _ ι' _ κ v P' d G J L L' N hv hP' hP hJ hL hL' _
  have hN : (fun j => fibreDeg κ (N j).a) = (Fin.elim0 : Fin 0 → FibreBlock κ → ℤ) :=
    funext fun j => j.elim0
  have hA : Fin.append L' N = L' := funext fun j => by
    rw [Fin.append_right_nil L' N rfl]
    rfl
  rw [hN, hA]
  exact hAI3 I hI K ι K' ι' κ v P' d G J L L' hv hP' hP hJ hL hL'

theorem PushforwardProjLineFlag.proof (hAI3 : PushforwardArithIntersection.Statement) (hStep : PFStep.Statement) : PushforwardProjLineFlag.Statement := by
  intro I hI K _ ι _ K' _ ι' _ κ v P' d r
  have key : ∀ r, PFAt I r := fun r =>
    Nat.rec (pfAt_zero hAI3 I hI) (fun r h => hStep I hI r h) r
  exact key r K ι K' ι' κ v P' d

end GroundTheory.Heights₂.Heights.Inter
