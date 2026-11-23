import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassEquivReferenceTupleEqSelfStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC.MuZeroForms

theorem law0_choose_mu0_eq_self : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (x : ((I.fm l u I.mu0).lat 0).V),
    (l0 u I.mu0).choose x = x := by
  intro B X I h l Z l0 u x
  apply (I.fm l u I.mu0).emb_inj 0
  rw [(l0 u I.mu0).choose_spec.2 x]
  show LinearEquiv.funCongrLeft ℂ _ (I.eCls0 l u I.mu0).symm ((I.fm l u I.mu0).emb 0 x) = _
  funext c
  rw [LinearEquiv.funCongrLeft_apply]
  show (I.fm l u I.mu0).emb 0 x ((I.eCls0 l u I.mu0).symm c) = _
  have hc : (I.eCls0 l u I.mu0).symm c = c :=
    (I.eCls0 l u I.mu0).symm_apply_eq.2 (GlobalTheory.T.eCls0_mu0_eq_self I h l u c).symm
  rw [hc]

end GlobalTheory.Mem.Col2.TC.MuZeroForms
