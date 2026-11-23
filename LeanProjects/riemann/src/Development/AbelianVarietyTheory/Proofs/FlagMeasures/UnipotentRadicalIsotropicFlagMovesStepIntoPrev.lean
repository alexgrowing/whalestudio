import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
open Formalism.MainNotions.S

namespace GlobalTheory

theorem unipRadical_moves_step_into_prev :
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
      [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V]
      [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r : ℕ} (Fr : Formalism.MainNotions.S.LocNG.FrameD H r)
      (n : V ≃ₗ[E] V), n ∈ Fr.N → ∀ j : ℕ, j ≤ r → ∀ v ∈ Fr.Fj j,
        n v - v ∈ Fr.Fj (j - 1) ∧ n.symm v - v ∈ Fr.Fj (j - 1) := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r Fr n hn j hj v hv
  have hs := Formalism.MainNotions.BridgeLemma.mem_NSet_of_mem_N Fr hn
  exact ⟨hs.2.1 j hj v hv, Formalism.MainNotions.BridgeLemma.NSet_inv_Fj Fr hs j hj v hv⟩

end GlobalTheory
