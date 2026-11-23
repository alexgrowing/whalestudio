import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
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
theorem _root_.GlobalTheory.T.weil_datum_transport_source_rational_isometry : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (d : HypDec S S₀ 0), IsStdChar D ψ (-1) → Function.Bijective d.emb0 ∧ Function.Bijective (d.ext0 T) ∧ (∀ f : WO S T → ℂ, IsThetaFunO ψ S₀ T (fun w => f (d.ext0 T w)) ↔ IsThetaFunO ψ S T f) ∧ ∀ (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ g h f, IsThetaFunO ψ S T f → om₀ (g, h) (fun w => f (d.ext0 T w)) = fun w => om (d.emb0 g, h) f (d.ext0 T w) := by
  first | exact @GlobalTheory.WeilSrc.om0_ext0_eq_om_emb0_of_isWeilDatumO | exact GlobalTheory.WeilSrc.om0_ext0_eq_om_emb0_of_isWeilDatumO | (intros; apply GlobalTheory.WeilSrc.om0_ext0_eq_om_emb0_of_isWeilDatumO <;> assumption)
