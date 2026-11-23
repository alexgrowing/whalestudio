import Formalism.LocalToGlobal.Divisibility.RecBridge
import Formalism.LocalToGlobal.GroupLattices.JointServices.ValIntNonneg
import Formalism.LocalToGlobal.GroupLattices.JointServices.PerTuple
import Formalism.SharpRestriction.Divisibility.ClosedSizeLink.DivisionAdmissibleFamilyOfData
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.Divisibility.HookProducts.Compl3Record

noncomputable section

namespace Formalism.L2.DIV.Wire

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.DIV

variable {eps : ℝ} {Fm : Formalism.MainNotions.FamP eps}

theorem la_of (Fm : Formalism.MainNotions.FamP eps) : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, 0 ≤ (Fm.L x i).La :=
  ⟨Fm.x1 + 1, fun x hx i => Formalism.MainNotions.DIV.La_nonneg (Fm.L x i) (Fm.sizes x (by linarith) i).2.2.2.2.2.2.1⟩

theorem za_of (Fm : Formalism.MainNotions.FamP eps) : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.L x i).ZeroAbove :=
  ⟨Fm.x1 + 1, fun x hx i => Formalism.MainNotions.WeightDegreeSizes.zero_gain_above_family Fm x (by linarith) i⟩

end Formalism.L2.DIV.Wire

end
