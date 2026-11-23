import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsBiSmooth

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7}

namespace Dat

variable {u : D.what₂.Word} (d : Dat D u)

def CommTo : Prop :=
  ∀ j, j ≤ D.R.m → ∃ (U : Col D u 0 →ₗ[ℂ] Col D u 0) (c : ℂ), (∀ ψ ∈ (D.mem u).A.Mram, U ψ ∈ (D.mem u).A.Mram) ∧
    (∀ ψ ∈ (D.mem u).A.Mram, U ψ = 0 → ψ = 0) ∧
    ∀ ψ ∈ (D.mem u).A.Mram, d.S j (GlobalTheory.Core.Rk.colTo (D.mem u).C j ψ) = c • GlobalTheory.Core.Rk.colTo (D.mem u).C j (U ψ)

structure LawsT : Prop where
  base : d.Base
  topOK : CoCpt D.sp.X'
  supp1 : d.Supp1
  supp2 : d.Supp2
  val : d.ValS
  valLast : d.ValLastS
  kerLift : d.KerLift
  perLast : d.PerLast
  topOnto : d.TopOnto
  rdLaw : d.RdLaw
  stab : d.Stab
  comm : d.CommTo
  bot : d.Bot

end Dat

def SeeSawT (D : D7) (u : D.what₂.Word) : Prop := ∃ d : Dat D u, d.LawsT

end GlobalTheory.SeeSaw

end
