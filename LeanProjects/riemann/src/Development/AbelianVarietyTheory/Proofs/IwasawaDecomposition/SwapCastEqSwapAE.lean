import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtId

variable {D : D7}

theorem idFrame_iff_unitFr {V : HSp D} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V V.rank) :
    GlobalTheory.MtRead.IdFrame hF P ↔ GlobalTheory.MtIn.UnitFr P := by
  constructor
  · rintro ⟨hn, h⟩ κ
    refine Units.ext (Matrix.ext fun a b => ?_)
    have := (RingEquiv.eq_symm_apply _).1 (h κ a b)
    exact this
  · intro h
    refine ⟨rfl, fun κ a b => (RingEquiv.eq_symm_apply _).2 ?_⟩
    exact congrArg (fun g : GL (Fin V.rank) (EAf D) => g.val a b) (h κ)

def castFr {V : HSp D} {n : ℕ} (hn : V.rank = n) (P : principalLevelFrame.RowPsi V V.rank) : principalLevelFrame.RowPsi V n := hn ▸ P

theorem idFrame_castFr {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (hn : V.rank = n)
    {P : principalLevelFrame.RowPsi V V.rank} (h : GlobalTheory.MtIn.UnitFr P) : GlobalTheory.MtRead.IdFrame hF (castFr hn P) := by
  subst hn
  exact (idFrame_iff_unitFr hF P).2 h

end GlobalTheory.MtId

end
