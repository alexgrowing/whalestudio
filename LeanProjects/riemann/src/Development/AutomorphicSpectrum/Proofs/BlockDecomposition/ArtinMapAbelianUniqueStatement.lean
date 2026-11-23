import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinMapAbelianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem
open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.artin_map_abelian_unique : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (Art Art' : Neutral.B1.IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K), Neutral.B1.IsGlobalArtinMap K Art → Neutral.B1.IsGlobalArtinMap K Art' → ∀ (L : IntermediateField K (AlgebraicClosure K)) (h : Neutral.B1.IsFiniteAbelian K L) (c : Neutral.B1.IdeleClassGroup K), Neutral.B1.abRestrict K L h (Art c) = Neutral.B1.abRestrict K L h (Art' c) := by
  first | exact @GlobalTheory.CompanionTheory.ArtinUniq.abRestrict_eq | exact GlobalTheory.CompanionTheory.ArtinUniq.abRestrict_eq | (intros; apply GlobalTheory.CompanionTheory.ArtinUniq.abRestrict_eq <;> assumption)
