import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairLatticeLeLiftedPairLatticeSupIsotropic
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairLattice_le_liftedPairLattice_sup_isotropic : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V), IsPair Λ F F' F'' β g → Mlat Λ F F' F'' β g ≤ La Λ g F F'' ⊔ toO S (Xsp F) := by
  first | exact @GlobalTheory.LoopC.PairLat.Mlat_le_La_sup | exact GlobalTheory.LoopC.PairLat.Mlat_le_La_sup | (intros; apply GlobalTheory.LoopC.PairLat.Mlat_le_La_sup <;> assumption)
