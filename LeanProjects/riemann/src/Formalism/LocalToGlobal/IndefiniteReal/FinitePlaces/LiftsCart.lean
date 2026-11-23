import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

noncomputable section

namespace Formalism.IndefR.Fin.Lifts

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix Formalism.L2.Theta
open scoped ComplexOrder
open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem posDef_of_sig {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.UG.HasSignature G n 0) : G.PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have hJ : Formalism.UG.Jpq n 0 = 1 := by
    unfold Formalism.UG.Jpq
    rw [show (-1 : Matrix (Fin 0) (Fin 0) ℂ) = 1 by ext i; exact i.elim0, Matrix.fromBlocks_one]
  have hc : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ) =
      star (P : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ) := by
    ext i j
    simp [Formalism.UG.cT, Matrix.star_apply]
  rw [hJ, hc] at hP
  have hU : IsUnit (P : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ) := P.isUnit
  have h1 : (G.reindex e e).PosDef := (Matrix.IsUnit.posDef_star_left_conjugate_iff hU).1 (hP ▸ Matrix.PosDef.one)
  have hG : G = (G.reindex e e).submatrix e e := by
    ext i j
    simp
  rw [hG]
  exact h1.submatrix e.injective

end Formalism.IndefR.Fin.Lifts

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Formalism.IndefR.Fin

end
