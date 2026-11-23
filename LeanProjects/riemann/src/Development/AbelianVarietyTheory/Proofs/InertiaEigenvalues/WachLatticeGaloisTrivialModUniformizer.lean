import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmulOfDvdRepr

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.WachLatticeTrivialModUniformizer

set_option maxHeartbeats 1000000 in

theorem wachLattice_galois_trivial_mod_uniformizer : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), P2 D HW F := by
  intro D HW F Cm l _ K s LL h T hT
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.NL.GamModX.gam_mod_π_mod_X D HW F Cm l K s LL h T hT
  refine ⟨(wach_gamma_stable_first _ T).1, (wach_gamma_stable_first _ T).2, fun x hx => ?_⟩
  obtain ⟨y, hy, e⟩ := h3 x hx
  exact ⟨y, hy, e.symm⟩

end GlobalTheory.NL.WachLatticeTrivialModUniformizer
