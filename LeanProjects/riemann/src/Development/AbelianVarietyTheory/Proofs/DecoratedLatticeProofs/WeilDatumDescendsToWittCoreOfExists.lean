import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem resEta_core {D : D7} {χ : (AE D)ˣ →* Circle} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (h : ResEta D χ S.rank) : ResEta D χ S₀.rank :=
  resEta_parity h (by rw [← d.rank_add]; omega)

theorem descent_of_weilDatumExists : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumExistenceCriterion.WeilDatumExists D → Descent D := by
  intro D hW ψ S T χS χT om h
  refine ⟨fun S₀ ρ d => ?_, fun T₀ ρ d => ?_⟩
  · exact hW S₀ T ψ χS χT h.std h.hecS h.hecT (resEta_core d h.resS) h.resT
  · exact hW S T₀ ψ χS χT h.std h.hecS h.hecT h.resS (resEta_core d h.resT)

end GlobalTheory.Unf

end
