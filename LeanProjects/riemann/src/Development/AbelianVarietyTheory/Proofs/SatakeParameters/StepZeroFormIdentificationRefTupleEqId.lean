import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AtTrue

theorem stepZeroFormIdentification_refTuple_eq_id : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word), (I.tw l l0 Z).e0 u (I.rec7 l Z).what₂.mu0 = (I.tw l l0 Z).eMu0 u 0 (Nat.zero_le _) := by
  intro B X I _ _ l Z l0 u
  apply LinearEquiv.ext
  intro x
  have h := (l0 u I.mu0).choose_spec.2 x
  rw [stepZeroTwist_reference_tuple_eq_id l u] at h
  exact (I.fm l u I.mu0).emb_inj 0 h

end GlobalTheory.TwU.AtTrue
