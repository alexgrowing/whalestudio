import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerMovedVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrChInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridFiniteDatumVectorThetaFockVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.AvgColJet

theorem fockIn_frC {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T} (hL : L.Is μ0)
    (W : G.Weil) {U : Set T} (N : Std G U) (t : T) (j : ℕ) (hj : j < D.R.m)
    (f : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ) (hf : IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) f)
    (Q : PolF D (G.pT (.top t j)).rank (G.pS (.top t j)).rank) :
    fockIn W N.frC (.top t j) f Q = W.fock (.top t j) f (AvgCol.frCh W N j Q) := by
  have hn : DefNode D.R.m (.top j) ∧ DefNode D.R.m (.top (j + 1)) :=
    ⟨show j ≤ D.R.m by omega, show j + 1 ≤ D.R.m by omega⟩
  have c1 : W.cart (.top j) = fun _ => 1 := funext (GlobalTheory.FockReal.cart_def hL W hn.1)
  have c2 : W.cart (.top (j + 1)) = fun _ => 1 := funext (GlobalTheory.FockReal.cart_def hL W hn.2)
  have e : ∀ X, DefNode D.R.m X → N.frC X = fun τ => W.onb X τ * AvgCol.frRel W N X τ := by
    intro X hX
    funext τ
    have hu : IsUnit (W.onb X τ).det := Matrix.isUnit_det_of_left_inverse (GlobalTheory.FockReal.onb_def hL W hX τ)
    rw [AvgCol.frRel, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  simp only [fockIn, GridData.Weil.fock, GridData.cartS, GridData.onT, GridData.onS, c1, c2, e _ hn.1, e _ hn.2]
  rw [GlobalTheory.FockBaseChange.pureTensorO_subst D W.ψ W.θ _ _ W.ψ_std W.θ_is _ _ _ _ f hf]
  rfl

theorem fockComp_frC_eq_jetOp : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m → ∀ (t : T) (d : FinDatum G t (.top t j)), S.Z.HasVec d →
    ∀ (x : FinPt G (.top j)) (y : FinPt G (.top (j + 1))),
      fockComp W S.N.frC (.top t j) (S.Z.vec d) (x * S.N.u _) (y * S.N.u _) =
        Formalism.L2.Ker.jetOp (wt G (.top j)) (wt G (.top (j + 1)))
          (fun m => W.ker (.top t j) (W.fock (.top t j) (movedVec t S d) (GlobalTheory.AvgCol.frCh W S.N j (MvPolynomial.monomial m 1)))
            (x : GA D (G.V (.top j))) (y : GA D (G.V (.top (j + 1)))))
          (nuEnd G (.top t j)) := by
  intro D T L sc G W U S μ0 hL j hj t d hd x y
  have hp : DefPair D.R.m (Pair.top t j : Pair T) := show j + 1 ≤ D.R.m by omega
  have hf := (GlobalTheory.FockRealVec.vec_theta_fock W S.Z hp d hd).1
  unfold fockComp
  refine congrArg (fun F => Formalism.L2.Ker.jetOp (wt G (.top j)) (wt G (.top (j + 1))) F (nuEnd G (.top t j))) (funext fun m => ?_)
  unfold jetTab kerFin
  have hid : m.mapDomain (fvar G (.top t j)) = m := Finsupp.mapDomain_id
  rw [hid, Subgroup.coe_mul, Subgroup.coe_mul, GlobalTheory.FockReal.ker_mul, fockIn_frC hL W S.N t j hj _ hf]
  congr 1
  exact GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ _ _ _ (W.om (.top t j)) (W.om_is (.top t j) (show j + 1 ≤ D.R.m by omega))
    W.θ W.θ_is _ (S.N.u _).2 _ (S.N.u _).2 _ _ _ _ _ _ hf

end GlobalTheory.AvgColJet
end
