import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylIntegralCovariance.IntEqFour
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTbijChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTwpAlg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTwpMeas
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTwSt

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.TW.Twp
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
open PositivityTheory.SiegelWeilFormula.TBij.Adp
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem int_eq_four_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ν : Measure (Mx F E d.m d.n)) (hν : d.IsCov ν) (ε : ℤˣ) (f : Mx F E d.m d.n → ℂ)
    (Y : Matrix (Fin d.m) (Fin d.n) E) :
    ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram (incM F Y) Z)) * f Z ∂ν =
      GroundTheory.Automorphic.GJMatrix.adelicFourierPi F (fun c => f (d.cmb c))
        (fun q => algebraMap F (AF F) (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.Lm_k d ε (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rc_k d Y) q)) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.integral_cov_k d ν hν, GroundTheory.Automorphic.GJMatrix.adelicFourierPi]
  congr 1
  funext c
  rw [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.pair_eq_k d ε Y (d.cmb c), _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_cmb, GlobalTheory.AdelicSvN.Weyl.isStd_eq d.ok.good.std, mul_comm]
theorem poisson_k : _root_.PositivityTheory.SiegelWeilFormula.TW.Poisson_k := by
  intro F E _ _ _ _ _ σ d ν hν ε f hf
  have hg : (fun c => f (d.cmb c)) ∈ schA F (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) := Submodule.mem_comap.1 hf
  have hθ := GlobalTheory.TowU.FourWeyl.theta_four hg
  refine (tsum_congr fun X => _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.int_eq_four_k d ν hν ε f X).trans ?_
  refine ((_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rc_k d).toEquiv.tsum_eq (fun a => GroundTheory.Automorphic.GJMatrix.adelicFourierPi F (fun c => f (d.cmb c))
      (fun q => algebraMap F (AF F) (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.Lm_k d ε a q)))).trans ?_
  refine ((LinearEquiv.ofInjectiveEndo (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.Lm_k d ε) (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.Lm_inj_k d ε)).toEquiv.tsum_eq
      (fun a => GroundTheory.Automorphic.GJMatrix.adelicFourierPi F (fun c => f (d.cmb c)) (fun q => algebraMap F (AF F) (a q)))).trans ?_
  refine hθ.trans ?_
  show ∑' ξ : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → F, f (d.cmb fun q => algebraMap F (AF F) (ξ q)) = _
  have e : ∀ X : Matrix (Fin d.m) (Fin d.n) E, f (incM F X) = f (d.cmb fun q => algebraMap F (AF F) (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rc_k d X q)) := by
    intro X
    congr 1
    rw [← _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd d (incM F X)]
    congr 1
    funext q
    rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_incM]
    rfl
  simp_rw [e]
  exact ((_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rc_k d).toEquiv.tsum_eq (fun a => f (d.cmb fun q => algebraMap F (AF F) (a q)))).symm
end PositivityTheory.SiegelWeilFormula.TW.Twp
end
end
