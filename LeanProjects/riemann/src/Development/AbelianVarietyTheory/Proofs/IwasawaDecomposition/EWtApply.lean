import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwP

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def eWt (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) :
    (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ) :=
  LinearEquiv.refl ℂ _

theorem eWt_apply (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (z : (I.per l u a).Wrow)
    (c : (I.fm l u a).clsP) (s : Formalism.L2.Forms.FrP (I.rec7 l Z)) (s' : GlobalTheory.Mem.Col2.Fr B.fields.emb B.embLL (B.R.N B.R.m - 1))
    (h : s'.1 = s.1) : eWt I l Z u a z c s = z c s' := by
  have e : s' = s := Subtype.ext h
  subst e
  rfl

end GlobalTheory.Mem.Col2.TwP

end
