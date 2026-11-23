import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QzTorsionZmodEmbedding
import Mathlib
import Formalism.GaloisCohomology.LocalTateDualityK
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qz_torsion_and_exists_zmod_pow_embedding : ∀ (l : ℕ) [Fact l.Prime], (∀ a : QZ l, ∃ r : ℕ, (l : ℤ_[l]) ^ r • a = 0) ∧ ∀ r : ℕ, ∃ ι : ZMod (l ^ r) →+ QZ l, Function.Injective ι ∧ (∀ a : QZ l, (l : ℤ_[l]) ^ r • a = 0 ↔ a ∈ Set.range ι) ∧ ∀ (x : ℤ_[l]) (y : ZMod (l ^ r)), ι (PadicInt.toZModPow r x * y) = x • ι y := by
  first | exact @GlobalTheory.qz_torsion_zmod_embedding | exact GlobalTheory.qz_torsion_zmod_embedding | (intros; apply GlobalTheory.qz_torsion_zmod_embedding <;> assumption)
