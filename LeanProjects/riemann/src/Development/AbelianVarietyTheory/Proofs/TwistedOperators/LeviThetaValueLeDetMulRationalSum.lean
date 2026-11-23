import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittSourceProof
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCoreOfExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
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
noncomputable section

namespace GlobalTheory.LeviThetaSum

theorem levi_sum : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec S S₀ r)
    (χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
    IsWeilDatumO ψ S T χS χT om →
    ∃ (μ' : Measure (Mx D T.rank r)) (𝓕' : Set (Mx D T.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D T.rank r) μ' 𝓕' ∧
      ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ α : GL (Fin r) (Formalism.L2.Theta.AE D),
        ‖om (d.levi α, 1) f 0‖ₑ ≤ ENNReal.ofReal (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank α) *
          ∑' ξ : Matrix (Fin T.rank) (Fin r) D.host.E,
            ‖d.mixS T ψ μ' 𝓕' f (HMul.hMul (ξ.map (incA D) : Mx D T.rank r) α.1) 0‖ₑ := by
  intro D ψ S S₀ T r d χS χT om ho
  obtain ⟨v⟩ := GlobalTheory.Unf.Inhab.nonempty_volM D T.rank r
  obtain ⟨om₀, ho₀⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ ho.std S₀ T χS χT
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) ho.hecS ho.hecT (GlobalTheory.Unf.resEta_core d ho.resS) ho.resT
  refine ⟨v.μ, v.𝓕, v.covol, fun f hf α => ?_⟩
  have hF := GlobalTheory.MixSourceFormulas.mixed_source D ψ S S₀ T r d χS χT om om₀ ho ho₀ v.μ v.𝓕 v.covol f hf
  have hg : IsThetaFunO ψ S T (om (d.levi α, 1) f) := ho.om_pres _ f hf
  have hsum := (GlobalTheory.HeisMixSource.heis_mixS D ψ ho.std S S₀ T r d v (om (d.levi α, 1) f) hg).2.2.2.2 0
  rw [map_zero] at hsum
  rw [← hsum.tsum_eq]
  refine enorm_tsum_le_tsum_enorm.trans (le_of_eq ?_)
  rw [← ENNReal.tsum_mul_left]
  congr 1
  funext ξ
  have e := congrFun (hF.levi α (GlobalTheory.MixModel.rat ξ)) 0
  rw [e, Pi.smul_apply, smul_eq_mul, enorm_mul, enorm_mul]
  congr 1
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Circle.norm_coe, ENNReal.ofReal_one, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod_pos _ _).le]

end GlobalTheory.LeviThetaSum

end
