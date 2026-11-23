import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFlagUnipotentMatrixIffJointlyBijectivePair
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFlagUnipotentMatrix_iff_jointlyBijective_pair : ∀ {A R₁ R₂ : Type} [CommRing A] [CommRing R₁] [CommRing R₂] (f : A →+* R₁) (g : A →+* R₂), (∀ y, f y = 0 → g y = 0 → y = 0) → (∀ a b, ∃ y, f y = a ∧ g y = b) → ∀ {n ρ : ℕ} (E : Matrix (Fin n) (Fin ρ) A) (K : Matrix (Fin ρ) (Fin n) A) (M : Matrix (Fin n) (Fin n) A), GlobalTheory.BesselChar.Unip E K M ↔ GlobalTheory.BesselChar.Unip (E.map f) (K.map f) (M.map f) ∧ GlobalTheory.BesselChar.Unip (E.map g) (K.map g) (M.map g) := by
  first | exact @GlobalTheory.BesselChar.JointSplit.unip_iff_of_joint | exact GlobalTheory.BesselChar.JointSplit.unip_iff_of_joint | (intros; apply GlobalTheory.BesselChar.JointSplit.unip_iff_of_joint <;> assumption)
