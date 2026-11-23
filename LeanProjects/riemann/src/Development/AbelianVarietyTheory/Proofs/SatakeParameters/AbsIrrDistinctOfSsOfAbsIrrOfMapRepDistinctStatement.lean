import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrrDistinctOfSsOfAbsIrrOfMapRepDistinct
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absIrrDistinct_of_isSS_absIrr_mapRep_nonIso : ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k), IsSSRep ρ → (∀ W, IsIrrSub ρ W → AbsIrrSub ρ W) → (∀ W₁ W₂, IsIrrSub (mapRep f ρ) W₁ → IsIrrSub (mapRep f ρ) W₂ → W₁ ⊓ W₂ = ⊥ → ¬ IsoSub (mapRep f ρ) W₁ W₂) → AbsIrrDistinct (matRep ((Units.coeHom _).comp ρ)) := by
  first | exact @GlobalTheory.absIrrDistinct_of_ss_of_absIrr_of_mapRep_distinct | exact GlobalTheory.absIrrDistinct_of_ss_of_absIrr_of_mapRep_distinct | (intros; apply GlobalTheory.absIrrDistinct_of_ss_of_absIrr_of_mapRep_distinct <;> assumption)
