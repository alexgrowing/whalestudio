import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AuxiliaryPrimeLtFirstTypePrimeOfSizes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SizesOfSizeRows
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DownFock

theorem isThetaFunO_fock_down : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (ρ : RealMatch W)
    (t : T) (i j : ℕ), i ≤ D.R.m → j < D.R.m → ∀ {e : AE D}, IsIdemSum e (locPl G t) →
    ∀ {φ f : WO (G.pS (.mu t i j)) (G.pT (.mu t i j)) → ℂ}, IsLocVec W (.mu t i j) e (vacOf ρ (.down t i j)) φ f →
    ∀ Q : PolF D (G.pT (.mu t i j)).rank (G.pS (.mu t i j)).rank,
      IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) (W.fock (.mu t i j) f Q) := by
  intro D T L sc G W ρ t i j hi hj e _he φ f hf Q
  have hv : IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.mu t i j)) (G.onT W.cart (.mu t i j))
      (G.latS (.mu t i j) : Set _) (G.latT (.mu t i j) : Set _) (ρ.vT i j) := ρ.vT_is t i j hi hj
  have hf' : IsThetaFunO W.ψ _ _ f :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is hf.2 hv.2.theta
  exact GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hf' Q

end GlobalTheory.DownFock
