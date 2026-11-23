import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SymplOHZeroRight
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SobSym
import Formalism.LocalToGlobal.IndefiniteReal.HaarTransfer.SobLeafP

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff ENNReal

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}

theorem dH_bdd {ψ : AddChar (AF D.host.F) ℂ} (hψu : ∀ a, ‖ψ a‖ = 1) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {L : (Fin k → ℝ) →+ WO S T} (hs : ∀ x, ContDiff ℝ ∞ (Gf ψ L f x)) {n : ℕ} (l : Fin n → Fin k)
    (hc : Continuous (dH ψ L l f)) : ∃ M, ∀ x, ‖dH ψ L l f x‖ ≤ M := by
  obtain ⟨K, hK, hFK⟩ := PHeisFC.FD_sub_compact T S
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨M, fun x => ?_⟩
  obtain ⟨g, hg, -⟩ := PHeisFC.exU T S x
  obtain ⟨γ, hγ⟩ := g.2
  have hgx : (g : WO S T) + x = ratW T S γ + x := by rw [← hγ]; rfl
  rw [← norm_dH_rat hψu hf hs l γ x, ← hgx]
  exact hM _ (hFK hg)

end Formalism.IndefR.Eqv

end
