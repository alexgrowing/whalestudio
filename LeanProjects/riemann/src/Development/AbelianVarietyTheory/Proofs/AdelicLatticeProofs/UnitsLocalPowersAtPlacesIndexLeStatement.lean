import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsLocalPowersAtPlacesIndexLe
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitsLocalPowersAtPlaces_index_le : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (S : Finset (HeightOneSpectrum (𝓞 F))), 0 < p → (finPow p F S).index ≠ 0 ∧ (finPow p F S).index ≤ p ^ (2 * (S.card + Fintype.card (InfinitePlace F))) := by
  first | exact @GlobalTheory.CNorm.index_finPow_le | exact GlobalTheory.CNorm.index_finPow_le | (intros; apply GlobalTheory.CNorm.index_finPow_le <;> assumption)
