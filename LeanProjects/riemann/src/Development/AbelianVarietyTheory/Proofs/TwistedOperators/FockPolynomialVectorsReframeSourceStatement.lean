import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorsReframeSource
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialVectors_reframeSource : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ, ∃ BS' : D.what₂.Tau → Matrix (Fin (reS S b).rank) (Fin (reS S b).rank) ℂ, (∀ τ, (BS' τ)ᴴ * gramAt D (reS S b) τ * BS' τ = (BS τ)ᴴ * gramAt D S τ * BS τ) ∧ ∀ (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ), pureTensorO ψ θ (reS S b) T (fun _ => 1) sT BS' BT (reF S T b f) P = reF S T b (pureTensorO ψ θ S T (fun _ => 1) sT BS BT f P) := by
  first | exact @GlobalTheory.AdSpan.pureTensorO_reF | exact GlobalTheory.AdSpan.pureTensorO_reF | (intros; apply GlobalTheory.AdSpan.pureTensorO_reF <;> assumption)
