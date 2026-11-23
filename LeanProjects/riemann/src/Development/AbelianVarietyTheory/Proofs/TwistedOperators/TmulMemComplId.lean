import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.XCharBF

variable {D : D7}

def complId (𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : AddSubgroup (AE D) :=
  AddSubgroup.closure {s | ∃ α ∈ intAf D.host.F, ∃ a ∈ 𝔠, s = pairA D.host.F 0 α ⊗ₜ[D.host.F] a}

theorem tmul_mem_complId {𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {α : Af D.host.F} (hα : α ∈ intAf D.host.F)
    {a : D.host.E} (ha : a ∈ 𝔠) : pairA D.host.F 0 α ⊗ₜ[D.host.F] a ∈ complId 𝔠 :=
  AddSubgroup.subset_closure ⟨α, hα, a, ha, rfl⟩

example : pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) ∈ complId (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  exact tmul_mem_complId (fun w => by rw [map_one]; exact one_mem _) (FractionalIdeal.one_mem_one _)

end GlobalTheory.XCharBF

end
