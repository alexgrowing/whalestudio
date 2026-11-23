import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PoincareSeriesCompactSupportThetaLaw
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareSeries_compactSupport_thetaLaw : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (h : WO A T → ℂ), Continuous h → HasCompactSupport h → (∀ u, {γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E | h (ratW T A γ + u) ≠ 0}.Finite) ∧ Continuous (fun u => ∑' γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E, ψ (symplOH A T (ratW T A γ) u) * h (ratW T A γ + u)) ∧ ∀ (γ₀ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), (∑' γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E, ψ (symplOH A T (ratW T A γ) (ratW T A γ₀ + u)) * h (ratW T A γ + (ratW T A γ₀ + u))) = ψ (-(symplOH A T (ratW T A γ₀) u)) * ∑' γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E, ψ (symplOH A T (ratW T A γ) u) * h (ratW T A γ + u) := by
  first | exact @GlobalTheory.PoincareLaw.poincare_law | exact GlobalTheory.PoincareLaw.poincare_law | (intros; apply GlobalTheory.PoincareLaw.poincare_law <;> assumption)
