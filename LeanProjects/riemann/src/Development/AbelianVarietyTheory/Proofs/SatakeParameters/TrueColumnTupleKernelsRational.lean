import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyLaws
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AtTrue

theorem tuple_kernels_rational : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (Tw : TwForms (I.rec7 l Z)), ColIn.JetsIn I → Tw = I.tw l l0 Z →
    ∀ (u : B.Word) (a : I.ι) j, j < B.R.m → (Tw.fm u a).KRat j := by
  intro B X I h _ l Z l0 Tw hJ hTw u a j hj
  subst hTw
  exact ((KerRat.kernels_rational I l Z h hJ
    (Or.inr (GlobalTheory.Core.Ht2.family_laws I h (base_fields_primes_ok B X).1 l Z))).2.2 l0 u a).1 j hj

end GlobalTheory.TwU.AtTrue
