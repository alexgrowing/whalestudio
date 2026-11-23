import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LatticeAreaPositivity.TwoTorsionOffKernelsExists
import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LatticeAreaPositivity.DensityIntegrableFundDomain
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstIsogeny
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.IsogenyFormulaInstance

noncomputable section

namespace Formalism.L2.Th1.F2

open Formalism.L2.GlobalTheoryTheory Formalism.MainNotions

theorem cm_example_holds : CmExample := by
  intro d hd h4
  refine ⟨⟨_, rfl⟩, fun x hx => ?_⟩
  have hc : 4 * ((1 : ℕ) : ℤ) * (((1 + d) / 4 : ℕ) : ℤ) = (1 : ℤ) ^ 2 + (d : ℤ) := by
    have : 4 * ((1 + d) / 4) = 1 + d := by omega
    push_cast
    have h2 : (4 : ℤ) * (((1 + d) / 4 : ℕ) : ℤ) = 1 + (d : ℤ) := by exact_mod_cast this
    push_cast at h2
    linarith
  have h := F.cmStable 1 1 _ d one_pos hd hc 0 1 x hx
  simpa using h

end Formalism.L2.Th1.F2
