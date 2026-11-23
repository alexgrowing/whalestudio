import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdPartialEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentTwistedGroupEndomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeStabilizerOfLocalIntegralInBasis
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Matrix

namespace GlobalTheory.CutProdLev

theorem cutGL_mem_St_of_mem_prodLev : ∀ {D : D7} {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (P : Finset (Pl D.host.E))
    {n' : P → ℕ} (h : ∀ w, n' w = n) (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))) (x : GL (Fin n) (Lev.EAf D)),
    x ∈ prodLev β P h K → ∀ (b : Lev.EAf D) (hb : b * b = b),
    (∀ w : Pl D.host.E, (∃ PP ∈ P, w.under (𝓞 D.host.F) = PP.under (𝓞 D.host.F)) → GlobalTheory.StdFrames.cpt (D := D) w b = 0) →
    GlobalTheory.UnitaryIdemCut.cutGL b hb x ∈ St β := by
  intro D n β P n' h K x hx b hb hb0
  apply StabilizerBasis.GlobalTheory.CompanionTheory.StabBasis.mem_St_of_inBasis_mem_KO
  intro w

  have hc : GlobalTheory.StdFrames.cpt (D := D) w b * GlobalTheory.StdFrames.cpt (D := D) w b = GlobalTheory.StdFrames.cpt (D := D) w b :=
    (map_mul (GlobalTheory.StdFrames.cpt (D := D) w) b b).symm.trans (congrArg _ hb)
  have h01 : GlobalTheory.StdFrames.cpt (D := D) w b = 0 ∨ GlobalTheory.StdFrames.cpt (D := D) w b = 1 := by
    have h' : GlobalTheory.StdFrames.cpt (D := D) w b * (GlobalTheory.StdFrames.cpt (D := D) w b - 1) = 0 := by
      rw [mul_sub, hc, mul_one, sub_self]
    rcases mul_eq_zero.mp h' with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)

  have hconj : (MulAut.conj β⁻¹).toMonoidHom (GlobalTheory.UnitaryIdemCut.cutGL b hb x) =
      GlobalTheory.UnitaryIdemCut.cutGL b hb ((MulAut.conj β⁻¹).toMonoidHom x) :=
    (GlobalTheory.UnitaryIdemCut.cutGL_conj b hb β⁻¹ x).symm
  have hloc : ∀ y : GL (Fin n) (Lev.EAf D), GlobalTheory.StdFrames.loc w (GlobalTheory.UnitaryIdemCut.cutGL b hb y) =
      GlobalTheory.UnitaryIdemCut.cutGL _ hc (GlobalTheory.StdFrames.loc w y) := fun y =>
    GlobalTheory.UnitaryIdemCut.bc_cutGL (GlobalTheory.StdFrames.cpt w) b hb _ hc rfl y
  rcases h01 with h0 | h1
  ·
    have e1 : ∀ g : GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion D.host.E w), GlobalTheory.UnitaryIdemCut.cutGL _ hc g = 1 := fun g => Units.ext (by
      rw [GlobalTheory.UnitaryIdemCut.cutGL_val, h0]
      simp)
    have e : GlobalTheory.FunObj.inBasis rfl β w (GlobalTheory.UnitaryIdemCut.cutGL b hb x) = 1 := by
      simp only [GlobalTheory.FunObj.inBasis, MonoidHom.comp_apply]
      rw [hconj, hloc, e1, map_one]
    rw [e]
    exact one_mem _
  ·

    unfold GlobalTheory.FunObj.prodLev at hx
    have hx2 := (Subgroup.mem_inf.mp hx).2
    rw [Subgroup.mem_iInf] at hx2
    have hx3 := hx2 w
    rw [Subgroup.mem_iInf] at hx3
    have hxw := Subgroup.mem_comap.mp (hx3 fun PP hPP e => by
      have h2 := hb0 w ⟨PP, hPP, e⟩
      rw [h1] at h2
      exact one_ne_zero h2)
    have e1 : ∀ g : GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion D.host.E w), GlobalTheory.UnitaryIdemCut.cutGL _ hc g = g := fun g => Units.ext (by
      rw [GlobalTheory.UnitaryIdemCut.cutGL_val, h1]
      simp)
    have e : GlobalTheory.FunObj.inBasis rfl β w (GlobalTheory.UnitaryIdemCut.cutGL b hb x) = GlobalTheory.FunObj.inBasis rfl β w x := by
      simp only [GlobalTheory.FunObj.inBasis, MonoidHom.comp_apply]
      rw [hconj, hloc, e1]
    rw [e]
    exact hxw

end GlobalTheory.CutProdLev
