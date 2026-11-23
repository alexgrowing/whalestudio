import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassInvariantDescentCoprimeLevelModPow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classInvariant_descent_coprimeLevel_modPow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l n Ma Mb : ℕ), l.Prime → 0 < Ma → 0 < Mb → 6 * l ∣ Ma → Nat.Coprime Ma Mb → ∀ f : X.Kˣ, Lev X (Ma * Mb) f → (∀ γ ∈ CongruenceSubgroup.Gamma Ma, ∃ g : X.Kˣ, Lev X (Ma * Mb) g ∧ X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n)) → ∃ h : X.Kˣ, Lev X Ma ((f : X.K) ^ 4 * (h : X.K) ^ (l ^ n)) := by
  first | exact @GlobalTheory.KZ.ES.CoprimeDescent.descent | exact GlobalTheory.KZ.ES.CoprimeDescent.descent | (intros; apply GlobalTheory.KZ.ES.CoprimeDescent.descent <;> assumption)
