import Formalism.LocalToGlobal.ProjectiveLattices.SpanRatSmulMem
import Formalism.LocalToGlobal.ProjectiveLattices.XcLat

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.QAt

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj.FJ

def MaxCuspsTieStatement : Prop :=
  ∀ (D : D7) (T : Core D) (j : ℕ) (cu : T.Cu j),
    WeightFamilies.dualZ D (T.Xc j cu) = (crdI 1 cu.1.2 : Set (Fin (WeightFamilies.rho D j) → D.host.E))

theorem maxCuspsTieStatement_holds : MaxCuspsTieStatement := by
  intro D T j cu
  have h1 : WeightFamilies.dualZ D (T.Xc j cu) = dualZE (XcFD 1 cu.1.2) := rfl
  rw [h1, dualZE_eq, xcFD_restrict]
  obtain ⟨ι, _, b, hb⟩ :=
    exists_basis (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) one_ne_zero cu.1.2
  rw [← hb, LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis _ (trBE_nondeg _) (trBE_symm _) b,
    hb, Submodule.coe_restrictScalars]

end Formalism.L2.Pj.QAt
