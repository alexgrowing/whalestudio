import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPresentationExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroPresZeroMod
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.FrobFilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_presentation_exists : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), ∀ (g : Γ(B.X, ⊤)), IsRootOfP p g p → ∀ R : Pres B, R.r = 1 → Kills g R.mod → ∃ R' : Pres B, IsFrob p R.mod R'.mod := by
  first | exact @GlobalTheory.FrobFilt.exists_pres_isFrob_of_rank_one | exact GlobalTheory.FrobFilt.exists_pres_isFrob_of_rank_one | (intros; apply GlobalTheory.FrobFilt.exists_pres_isFrob_of_rank_one <;> assumption)
