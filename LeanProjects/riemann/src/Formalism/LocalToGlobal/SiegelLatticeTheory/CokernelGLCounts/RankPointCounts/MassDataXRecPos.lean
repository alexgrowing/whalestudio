import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataPos
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXLeaves
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StabFiniteOf

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets

namespace Formalism.L2.SG.Pf.MassDataX

theorem massH_pos {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    0 < massH X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (frameOf X u) := by
  classical
  have hC := Formalism.L2.SG.Pf.MassDataX.classFinite_holds X u
  have hS := MassDataMassesW.stabFinite_of Formalism.L2.SG.Pf.MassDataX.hinfCompact_holds
    Formalism.L2.SG.Pf.MassDataX.kCompactOpen_holds X u
  show 0 < massCl (MassDataMassesW.GamH X u) (MassDataMassesW.KH X u)
  unfold massCl
  haveI := hC
  letI : Fintype (DoubleCoset.Quotient (G := ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))
      (MassDataMassesW.GamH X u : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))
      (MassDataMassesW.KH X u : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))) :=
    Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  apply Finset.sum_pos
  · intro c _
    haveI := hS (Quotient.out c)
    apply inv_pos.mpr
    exact_mod_cast Nat.card_pos
  · exact Finset.univ_nonempty_iff.mpr ⟨Quot.mk _ 1⟩

theorem finrank_Vpi_pos {D : D7} (X : HidaSetting D) (u : D.what₂.Word) : 0 < Module.finrank ℂ (X.Vpi u) := by
  classical
  have hx : ∀ v, ∃ y : X.Vloc u v, y ≠ 0 := fun v => by
    haveI := (X.piLoc_type u v).1
    exact exists_ne 0
  choose x hx using hx
  have hne : X.tensU u x ≠ 0 := by
    intro h0
    have h := X.tensU_inner u x x
    rw [h0, inner_zero_left] at h
    exact (Finset.prod_ne_zero_iff.mpr fun v _ => inner_self_ne_zero.mpr (hx v)) h.symm
  exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne⟩

end Formalism.L2.SG.Pf.MassDataX
