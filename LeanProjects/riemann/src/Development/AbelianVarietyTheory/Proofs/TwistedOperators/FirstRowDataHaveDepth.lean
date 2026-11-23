import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetVectorsNonzeroDepthFockVacuaStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockVectorsChainIsVacuumOffThetaLevels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVecto
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.FirstRowDepth

theorem datumDep : GlobalTheory.SepRows.DatumDep := by
  intro D hq T L μ0 hL sc G W M hM ρ Φ i
  obtain ⟨-, ⟨hth, hlat⟩, -⟩ := GlobalTheory.T.coset_vectors_nonzero_depth_fock_vacua D hq T L μ0 hL sc G W M hM i.1 i.2 (Φ i)
  have hthP : ∀ P, IsThetaFunO W.ψ (G.pS (.chi i.1 0)) (G.pT (.chi i.1 0))
      (W.fock (.chi i.1 0) (W.cosVec i (Φ i)) P) := fun P =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hth P
  refine ⟨hthP (ρ i), fun u hu => ?_, fun e he u hu hh => ?_⟩
  · exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite W.ψ W.θ _ _ W.θ_is _ _ _ _ _ hthP (2 • u)
      (GlobalTheory.VacGood.infPart_latO (AddSubgroup.nsmul_mem _ hu 2).1) (hlat.1 u hu) (ρ i)
  · exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite W.ψ W.θ _ _ W.θ_is _ _ _ _ _ hthP u
      (GlobalTheory.VacGood.infPart_latO hu.1) (hlat.2 e he u hu hh) (ρ i)

end GlobalTheory.FirstRowDepth

end
