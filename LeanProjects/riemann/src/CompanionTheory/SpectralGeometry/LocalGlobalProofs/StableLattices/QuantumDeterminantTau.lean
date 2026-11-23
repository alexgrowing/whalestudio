import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.HeckeDuality.GlRelTau
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CapPhi
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantEquality

noncomputable section

namespace GlobalTheory.CompanionTheory.CapelliTwist

open Formalism.REAL (qdet)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open CompanionTheory.RgExh.Hk

theorem qdetTau : QdetTau := by
  intro n X u
  have hgl : GlRelR X.E := X.gl
  have hrow : capelliC X.E (-u + ((n : ℂ) - 1)) = rminor X.E id id ((n : ℂ) - 1 - u) := by
    rw [show -u + ((n : ℂ) - 1) = (n : ℂ) - 1 - u by ring]
    exact cminor_eq_rminor X.E hgl id id _
  rw [GlobalTheory.CompanionTheory.RgExhHecke.qdet_eq_capelliC, GlobalTheory.CompanionTheory.RgExhHecke.qdet_eq_capelliC, hrow]
  show capelliC (fun a b => -X.E b a) u = _
  rw [ReciprocityTheory.ChartRestriction.DS.S7.CapPhi.capelliC_negT]
  rw [show ((-1 : Module.End ℂ X.V)) ^ n = algebraMap ℂ _ ((-1 : ℂ) ^ n) by simp,
    Algebra.smul_def]

end GlobalTheory.CompanionTheory.CapelliTwist
