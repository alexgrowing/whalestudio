import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDetLiftLocal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEqAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointsTiedS

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.Mem.JointsTrue
open Formalism.L2 Formalism.L2.Host ReciprocityTheory.Neutral.Bridge.HCFR
set_option maxHeartbeats 1000000 in
theorem joints_of_standard_character : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (T : _root_.Formalism.L2.TiedDataSAlt ex), I.StdC l Z T.cols → I.StdDt l Z T.full.1.base.dt → T.n.cf = I.cf l Z → (∀ a, T.chrDt.eDt a = (QuotientGroup.mk a : DtQ B.host I.SQ)) → Nonempty (Formalism.L2.Host.DivisorCharacterCompatibility (I.rec7 l Z) T.n.cf ex.nch T.n.tp Y) → Formalism.L2.Theta.IsStdChar (I.rec7 l Z) T.theta.W.ψ (-1) → _root_.Formalism.L2.JointsSAlt T := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex T hC hD hcf he hdiv hψ
  refine ⟨fun P e hi k y hy x hx => ?_, fun k => ?_, fun k v h a n hn ha => ?_, fun k v h ε hε c y hc => ?_, hdiv⟩
  · exact (hD x _ (isDetLift_local (I.rec7 l Z) P e hi k y hy x hx)).trans (he _).symm
  · rw [hcf, show (T.cols.forms (I.rec7 l Z).u₀).gl.piG = X.piG from (hC _).gl.piG]
    exact GlobalTheory.Core.Cls.JointsStd.piBar_std I hOk k
  · rw [hcf]
    exact GlobalTheory.Core.Cls.JointsStd.om_std I hOk l Z _ (hC _).gl k v h a n hn ha
  · have hy : algebraMap (I.rec7 l Z).host.F (v.adicCompletion (I.rec7 l Z).host.F) (y : (I.rec7 l Z).host.F) ∈
        v.adicCompletionIntegers (I.rec7 l Z).host.F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap]
      exact HeightOneSpectrum.valuation_le_one v y
    have e1 := GlobalTheory.Mem.TypePrimes.psiG_true I hOk hP l Z _ (hC (I.rec7 l Z).u₀).gl _ hψ k v h ε hε c y hc ⟨_, hy⟩ rfl
    unfold Joints.redV
    rw [dif_pos hy]
    exact e1
end GlobalTheory.Mem.JointsTrue
end
end
