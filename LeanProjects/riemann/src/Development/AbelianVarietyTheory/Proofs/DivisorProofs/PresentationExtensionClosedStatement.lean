import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresentationExtensionClosed
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroPresZeroMod
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.FrobFilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.presentation_extension_closed : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), ∀ S : ShortComplex B.X.Modules, S.ShortExact → (∃ P : Pres B, Nonempty (S.X₁ ≅ P.mod)) → (∃ P : Pres B, Nonempty (S.X₃ ≅ P.mod)) → ∃ P : Pres B, Nonempty (S.X₂ ≅ P.mod) := by
  first | exact @GlobalTheory.FrobFilt.ExtPres.exists_pres_of_shortExact | exact GlobalTheory.FrobFilt.ExtPres.exists_pres_of_shortExact | (intros; apply GlobalTheory.FrobFilt.ExtPres.exists_pres_of_shortExact <;> assumption)
