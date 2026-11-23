import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical

namespace GlobalTheory

theorem atLin_adCoef_eq_stdSer : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), atLin (Formalism.L2.Ker.adCoef lam P P') (fun j => MvPowerSeries.X j) F = stdSer D lam (fun _ => 1) P P' F := by
  intro D p _ lam N N' P P' F
  unfold stdSer
  congr 1
  funext k j
  rw [one_mul]
  unfold Formalism.L2.Ker.adCoef chgB
  dsimp only
  split_ifs with h
  · rw [h]
  · rfl

end GlobalTheory
