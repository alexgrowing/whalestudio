import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Interface
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.IsIntegralOfRoot
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFixJ
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModInertKur

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem jUnram (hH : _root_.Neutral.HilbertClassField.Statement) (hC : ChebOmSt) : JUnram := by
  intro d L hsf hd hL l _ hl hld ι
  obtain ⟨x, hx, -⟩ := exists_Om d (cm1 d L hsf hd hL)
  rw [← hx]
  exact inertKur (by omega) hld ι x fun σ hσ => fixJ hH hC hsf hd hL x hx σ (inertiaEl_mem_hilbert hσ)

end ReciprocityTheory.ChartRestriction.L1
