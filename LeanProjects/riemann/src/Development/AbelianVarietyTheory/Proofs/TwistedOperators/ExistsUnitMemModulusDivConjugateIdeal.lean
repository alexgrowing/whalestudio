import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualHomLatticeModulusShiftLocalEqLatO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.ShiftUnit

theorem exists_d : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (v : GlobalTheory.FinPl.Pl D), v ∉ G.pl.S0 → ∃ d : 𝓞 D.host.F, d ∉ v.asIdeal ∧ ((d : D.host.F) : D.host.E) ∈ shiftId G ∧ ∀ x ∈ shiftId G, ∃ y : 𝓞 D.host.E, (y : D.host.E) = ((d : D.host.F) : D.host.E) * x := by
  intro D T L sc G v hv
  obtain ⟨c, hcv, hc, hcb⟩ := GlobalTheory.BigLoc.exists_c G.pl sc hv
  have hne : G.pl.modulBar sc ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hcb
    apply GlobalTheory.IdeleAA.coe_ne_zero v c hcv
    rw [← GlobalTheory.BigLoc.coe_alg, hcb, map_zero]
  have h0 : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
  refine ⟨c, hcv, ?_, fun x hx => ?_⟩
  · unfold shiftId
    rw [← mul_one ((c : D.host.F) : D.host.E)]
    exact FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).2 ⟨_, hc, GlobalTheory.BigLoc.coe_alg c⟩)
      (FractionalIdeal.one_mem_inv_coe_ideal hne)
  · have hm : ((c : D.host.F) : D.host.E) * x ∈
        ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      have := FractionalIdeal.mul_mem_mul
        ((FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).2 ⟨_, hcb, GlobalTheory.BigLoc.coe_alg c⟩) hx
      rwa [shiftId, mul_left_comm, mul_inv_cancel₀ h0, mul_one] at this
    obtain ⟨o, -, ho⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).1 hm
    exact ⟨o, ho⟩

end GlobalTheory.ShiftUnit
