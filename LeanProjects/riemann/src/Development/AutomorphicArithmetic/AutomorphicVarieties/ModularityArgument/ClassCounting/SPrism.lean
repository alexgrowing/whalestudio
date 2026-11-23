import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.ToInhPartialProd

namespace UpperTheory.V.ZK

theorem sPrism : SPrism := by
  intro A _ G _ k m z
  obtain ⟨y, rfl⟩ := toInh_surjective A (m + 1) z
  rw [prism_toInh, bd_toInh, bd_toInh, prism_toInh, conj_toInh, ← map_add, ← map_sub, hbd_hprism]

end UpperTheory.V.ZK
