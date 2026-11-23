import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Columns.PathCountSymmetricHolds
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.HFld

open Classical in

def chiC {B : Base} {px : PreX B.toPre} (I : Col2.ColIn B px) :
    Fin B.R.m → IsDedekindDomain.HeightOneSpectrum (𝓞 B.host.E) → 𝓞 B.host.E → ℂ :=
  fun j w y =>
    if h : w ∈ (B.primes px).vGs then
      if hu : IsUnit (Ideal.Quotient.mk w.asIdeal y) then B.embLL ((I.Ch.chi j ⟨w, h⟩ hu.unit : B.LLˣ) : B.LL) else 0
    else 0

open Classical in

def qC {B : Base} {px : PreX B.toPre} (I : Col2.ColIn B px) :
    Formalism.L2.Host.HChar B.host.E → Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 B.host.E)) :=
  fun ξ => if h : ∃ a, I.xi a = ξ then I.Q h.choose else ∅

def SameCfg (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px) (B' : Base) (px' : PreX B'.toPre) (I' : Col2.ColIn B' px') : Prop :=
  B.toPre = B'.toPre ∧ HEq I.C I'.C ∧ HEq (Set.range I.xi) (Set.range I'.xi) ∧ HEq px.piG px'.piG ∧ HEq (chiC I) (chiC I') ∧
    HEq (qC I) (qC I')

end GlobalTheory.Mem.HFld

end
