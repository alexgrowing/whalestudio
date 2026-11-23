import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueBaseChangeEqOfMem

open TensorProduct

namespace GlobalTheory.FFDescent

theorem invertible_of_invertible_baseChange : ∀ (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B']
    [IsNoetherianRing B] [Module.FaithfullyFlat B B']
    (M : Type) [AddCommGroup M] [Module B M], Module.Invertible B' (B' ⊗[B] M) → Module.Invertible B M := by
  intro B B' _ _ _ _ _ M _ _ h
  exact (GlobalTheory.FlatDescent.invertible_baseChange_iff B' M).1 h

end GlobalTheory.FFDescent
