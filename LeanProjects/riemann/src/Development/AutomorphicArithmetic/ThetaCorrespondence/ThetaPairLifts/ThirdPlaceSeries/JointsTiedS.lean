import Formalism.LocalToGlobal.RatioJoints.CharacterProductEqOne
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEqAlt

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.UG
open scoped TensorProduct
namespace Formalism.L2
open Formalism.L2.Joints
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}
structure JointsSAlt {ex : Extra D L hT Gi Gl K Y cX} (T : _root_.Formalism.L2.TiedDataSAlt ex) : Prop where
  dt : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D), Formalism.L2.JoinChr.IsPlIdem D e P →
    ∀ (k : D.host.Eˣ) (y : Formalism.L2.Theta.AE D), IsRatioAt D e (k : D.host.E) y →
    ∀ x : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm,
      ((Matrix.GeneralLinearGroup.det (x : GL (Fin 1) (D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F)) :
        (D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F)ˣ) : D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F) = finE D y →
      T.full.1.base.dt x = T.chrDt.eDt (localIdele D.host.E P (Formalism.L2.Host.atFin P k))
  piBar : ∀ k : Fin 2, InPrimeK D (Formalism.L2.Forms.sigD D ((T.cols.forms D.u₀).gl.piG k : D.host.E)) (T.n.cf.P.pb k)
  om : ∀ (k : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (D.host.g k : 𝓞 D.host.F) ∈ v.asIdeal) (a n : ℕ)
    (hn : n.Coprime (D.host.g k)), a < D.R.m →
    (T.cols.forms D.u₀).gl.chiB k v h a (n : Formalism.L2.Forms.kv D.host.F v) =
      ((T.n.cf.W.om k (ZMod.unitOfCoprime n hn) ^ (2 * (a + 1)) : ℂˣ) : ℂ)
  psiG : ∀ (k : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (D.host.g k : 𝓞 D.host.F) ∈ v.asIdeal)
    (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F), Formalism.L2.Theta.IsPlaceIdem D v ε → ∀ c y : 𝓞 D.host.F,
    Valued.v (algebraMap D.host.F (v.adicCompletion D.host.F) (c : D.host.F) -
        (T.cols.forms D.u₀).gl.phi k v h (inclE (F := D.host.F) (v.adicCompletion D.host.F) D.host.xi0)) < 1 →
    (T.cols.forms D.u₀).gl.psi0 k v h (redV D.host.F v (algebraMap D.host.F (v.adicCompletion D.host.F) (y : D.host.F))) =
      T.theta.W.ψ (ε * algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ((c : D.host.F) * (y : D.host.F) / (D.host.g k : D.host.F)))
  div : Nonempty (Formalism.L2.Host.DivisorCharacterCompatibility D T.n.cf ex.nch T.n.tp Y)
namespace JointsS
variable {ex : Extra D L hT Gi Gl K Y cX} {T : _root_.Formalism.L2.TiedDataSAlt ex}
theorem _root_.Formalism.L2.JointsSAlt.idem (_ : _root_.Formalism.L2.JointsSAlt T) (P : HeightOneSpectrum (𝓞 D.host.E)) : ∃ e, Formalism.L2.JoinChr.IsPlIdem D e P :=
  T.sameChr.idem P
end JointsS
section
end
end Formalism.L2
end
end
