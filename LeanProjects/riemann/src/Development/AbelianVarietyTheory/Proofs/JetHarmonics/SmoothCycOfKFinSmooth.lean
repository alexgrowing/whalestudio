import Mathlib
import Formalism.PeriodIntegrals.LowCyc
import Formalism.PeriodIntegrals.KFinSmooth
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousWordTranslate

noncomputable section

open Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothCyclicApprox

open Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.GardingVec GlobalTheory.SmoothCyclic

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem contDiff_expProd_entry {k : ℕ} (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod a b :=
  (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)).contDiff.comp (contDiff_expProd Xs)

end

section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem smoothVec_of_smoothOnH {G : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G) {v : H}
    (hv : PI.UpqRep.SmoothOnH G fun g => σ g v) : SmoothVec {X | Xᴴ * G + G * X = 0} σ v := by
  intro k Xs hX
  have hp : ContDiff ℝ ∞ fun t : Fin k → ℝ => (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod :=
    contDiff_pi.2 fun a => contDiff_pi.2 fun b => contDiff_expProd_entry Xs a b
  have hm : ∀ t : Fin k → ℝ, PI.UpqRep.inUH G (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod := fun t =>
    list_prod_mem (G := G) _ fun g hg => by
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
      exact exp_mem hG (hX i) _
  refine contDiff_iff_contDiffAt.2 fun t => ?_
  obtain ⟨U, F, hU, htU, hF, hfF⟩ := hv _ (hm t)
  refine ((hF.contDiffAt (hU.mem_nhds htU)).comp t hp.contDiffAt).congr_of_eventuallyEq ?_
  filter_upwards [hp.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds htU)] with s hs
  exact hfF _ hs (hm s)

end

end GlobalTheory.SmoothCyclicApprox
