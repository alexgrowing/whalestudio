import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralContinuousStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralLocallySummableBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoissonSummationHermitianLatticeStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.HermitianIntegrability.UntupTupOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.HermitianIntegrability.ExistsSchwartzOfIsSchwartzArch
import Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.HermitianIntegrability.ExistsIntegralEqMul
import Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.HermitianIntegrability.IntegrableOfAddEquiv
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.PfWsf.Hand.TupleUntupling

variable {D : D7}

theorem integrable_of_hermE {r : ℕ} (lam : Measure (hermA D r)) (hlam : lam.IsAddHaarMeasure)
    (db : Measure (HermR (AF D.host.F) D.sp.cm.sig r)) (hdb : db.IsAddHaarMeasure)
    (f : HermR (AF D.host.F) D.sp.cm.sig r → ℂ) (hf : Integrable (fun b => f (hermE D r b)) lam) :
    Integrable f db :=
  PositivityTheory.PfWsf.Jab.WsInteg.integrable_of_hermE lam hlam db hdb f hf

theorem hermitian_unfolding_integral (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (θ : InfFam D)
    (hθ : IsInfFam θ) (μ : Measure (Mx D V.rank r)) (hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕)
    (lam : Measure (hermA D r)) (hlam : ∃ 𝓖, IsCovolOneH lam 𝓖) (hr : 2 * r < V.rank)
    (dx : Measure (Fin r → Fin V.rank → AE D)) (hdx : dx.IsAddHaarMeasure)
    (db : Measure (HermR (AF D.host.F) D.sp.cm.sig r)) (hdb : db.IsAddHaarMeasure)
    (Φ : (Fin r → Fin V.rank → AE D) → ℂ)
    (hΦ : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (F := D.host.F) (E := D.host.E) Φ) :
    Integrable (starN D.sp.cm.sig V.gram ψ dx Φ) db := by
  have hφ := mem_schwartzA_of_sb θ hθ Φ hΦ
  obtain ⟨𝓖, h𝓖⟩ := hlam
  have hJ : Integrable (Jt ψ V μ fun y => Φ (untup y)) lam :=
    (GlobalTheory.T.poisson_summation_hermitian_lattice D r ψ hψ lam 𝓖 h𝓖 _ (GlobalTheory.T.theta_integral_continuous D r V ψ θ μ _ hψ hθ hμ hφ)
      (GlobalTheory.T.theta_integral_locally_summable_bound D r V ψ θ μ _ hr hψ hθ hμ hφ)).1
  obtain ⟨c, hc⟩ := starN_hermE V ψ μ hμ.choose_spec.1 dx hdx
  refine integrable_of_hermE lam h𝓖.1 db hdb _ ?_
  simp only [hc]
  exact hJ.const_mul c

end PositivityTheory.PfWsf.Hand.TupleUntupling
