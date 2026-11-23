import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowClaim

theorem isThetaFunO_fock_movedVec_top {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {U : Set T} (S : GridChoice W U) {j : ℕ} (hj : j < D.R.m)
    (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank) (t : T) (d : FinDatum G t (.top t j))
    (hd : S.Z.HasVec d) :
    IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) (W.fock (.top t j) (movedVec t S d) Q) := by
  have hr : (Pair.top t j : Pair T).InRange D.R.m := by
    show j + 1 ≤ D.R.m
    omega
  have hω := W.om_is _ hr
  obtain ⟨f, hf⟩ := hd
  have hf0 : IsThetaFunO W.ψ _ _ f :=
    GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is hf ((S.Z.vac_is (.top t j) (show j + 1 ≤ D.R.m by omega)).2.theta)
  have hv : IsThetaFunO W.ψ _ _ (S.Z.vec d) := by
    rw [Normal.vec, FinDatum.vec_eq W hf]
    exact hω.om_pres _ _ hf0
  have hm : IsThetaFunO W.ψ _ _ (movedVec t S d) := hω.om_pres _ _ hv
  exact GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hm Q

theorem kerA_col_aut_cont : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m →
    ∀ (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank) (t : T), t ∈ U → ∀ (d : FinDatum G t (.top t j)), S.Z.HasVec d →
    (∀ γ ∈ GQ (G.V (.top j)), ∀ g h, W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) (γ * g) h =
      W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) g h) ∧
    ∀ z h, Continuous fun k : GinfC (G.V (.top j)) =>
      W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) (z * k) h := by
  intro D T L sc G W U S μ0 _ j hj Q t _ d hd
  have hr : (Pair.top t j : Pair T).InRange D.R.m := by
    show j + 1 ≤ D.R.m
    omega
  have hω := W.om_is _ hr
  have hF := isThetaFunO_fock_movedVec_top S hj Q t d hd
  refine ⟨fun γ hγ g h => ?_, fun z h => ?_⟩
  · show thetaKO (W.om (.top t j)) (γ * g) h _ = thetaKO (W.om (.top t j)) g h _
    have e : ((γ * g, h) : GA D (G.V (.top j)) × GA D (G.V (.top (j + 1)))) = (γ, 1) * (g, h) := by simp
    unfold thetaKO
    rw [e, map_mul]
    exact hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ hF)
  · show Continuous fun k : GinfC (G.V (.top j)) => thetaKO (W.om (.top t j)) (z * k) h _
    exact (hω.om_cont _ hF 0).comp ((continuous_const.mul continuous_subtype_val).prodMk continuous_const)

end GlobalTheory.RowClaim

end
