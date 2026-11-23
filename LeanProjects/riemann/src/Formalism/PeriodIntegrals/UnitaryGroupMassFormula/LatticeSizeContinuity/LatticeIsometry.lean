import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.LatSizeContOfSteps
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob

noncomputable section

open NumberField
open scoped TensorProduct
open PI.LatSizeCont

namespace PI.UnitaryGroupMassFormula.LSC

namespace LatIs

theorem lamAf_eq (I : Formalism.MainNotions.S.AutInst) :
    I.Lf = Formalism.UG.latS (F := I.F) (Formalism.MainNotions.S.Af I.F) (Formalism.MainNotions.S.IntAf I.F I.E) I.L := by
  show Formalism.MainNotions.S.lamAf (F := I.F) I.L = _
  unfold Formalism.MainNotions.S.lamAf Formalism.UG.latS
  congr 1
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem latSet_eq (I : Formalism.MainNotions.S.AutInst) (x : I.GA) :
    Size.latSet I x = (Formalism.UG.CS.globLat (F := I.F)
      (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) I.L : Set (Fin I.n → I.E)) := by
  ext u
  simp only [Size.latSet, Set.mem_setOf_eq, SetLike.mem_coe]
  rw [lamAf_eq]
  rfl

end LatIs

theorem lattice_isometry : LatIs := by
  intro I x
  have hL := Formalism.UG.P.global_lattice_isLattice_holds I.F I.E (Fin I.n) I.L (Module.Finite.iff_fg.2 I.L_fg)
    I.L_span (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F))
  exact ⟨_, hL.fg, hL.span_eq_top, LatIs.latSet_eq I x⟩

end PI.UnitaryGroupMassFormula.LSC
