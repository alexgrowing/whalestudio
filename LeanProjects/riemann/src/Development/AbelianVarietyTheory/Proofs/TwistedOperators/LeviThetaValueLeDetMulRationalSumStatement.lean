import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviThetaValueLeDetMulRationalSum
import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviThetaValue_le_det_mul_rational_sum : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec S S₀ r)
    (χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
    IsWeilDatumO ψ S T χS χT om →
    ∃ (μ' : Measure (Mx D T.rank r)) (𝓕' : Set (Mx D T.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D T.rank r) μ' 𝓕' ∧
      ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ α : GL (Fin r) (Formalism.L2.Theta.AE D),
        ‖om (d.levi α, 1) f 0‖ₑ ≤ ENNReal.ofReal (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank α) *
          ∑' ξ : Matrix (Fin T.rank) (Fin r) D.host.E,
            ‖d.mixS T ψ μ' 𝓕' f (HMul.hMul (ξ.map (incA D) : Mx D T.rank r) α.1) 0‖ₑ := by
  first | exact @GlobalTheory.LeviThetaSum.levi_sum | exact GlobalTheory.LeviThetaSum.levi_sum | (intros; apply GlobalTheory.LeviThetaSum.levi_sum <;> assumption)
