import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShEqvTw
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eqv_spMap_tw_of_isUnit : ∀ (q : ℕ) (i : ℤ) (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B), SH A → SH B → IsUnit (q : A) → Eqv _ (spMap φ) (tw q i) := by
  first | (exact @GlobalTheory.EtC.sh_eqv_tw) | (exact GlobalTheory.EtC.sh_eqv_tw) | (intros; apply GlobalTheory.EtC.sh_eqv_tw  <;> assumption)
