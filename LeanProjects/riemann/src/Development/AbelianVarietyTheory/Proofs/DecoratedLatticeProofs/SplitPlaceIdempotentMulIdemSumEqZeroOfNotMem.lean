import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.OutsideOrth

theorem mul_eq_zero : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D),
    PP ∉ P → Formalism.L2.NTheta.IsIdemAt p.e PP → IsIdemSum e P → e * p.e = 0 := by
  intro D k _ _ _ _ p P PP e hPP hp he
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun P' hP' => ?_
  rw [mul_comm]
  exact Formalism.IndefR.Fin.idem_orth (Formalism.IndefR.Fin.idemAt_split hp) hp (hes P' hP')
    (fun h => hPP (h ▸ hP'))

end GlobalTheory.LocMod.OutsideOrth
