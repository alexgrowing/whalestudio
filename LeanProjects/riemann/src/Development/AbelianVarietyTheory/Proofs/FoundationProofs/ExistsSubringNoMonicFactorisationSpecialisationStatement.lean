import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSubringNoMonicFactorisationSpecialisation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subring_no_monic_factorisation_specialisation : ∀ {F : Type} [Field F] [IsAlgClosed F] (Φ : Polynomial (Polynomial F)), Φ.Monic → Irreducible Φ → ∃ s : Finset F, ∃ Ψ : Polynomial (Polynomial (Subring.closure (s : Set F))), Ψ.map (Polynomial.mapRingHom (Subring.closure (s : Set F)).subtype) = Φ ∧ ∀ (k : Type) [Field k] (φ : Subring.closure (s : Set F) →+* k) (A B : Polynomial (Polynomial k)), A.Monic → B.Monic → A * B = Ψ.map (Polynomial.mapRingHom φ) → A.natDegree = 0 ∨ B.natDegree = 0 := by
  first | exact @GlobalTheory.FactorCertificate.exists_subring_no_monic_factorisation | exact GlobalTheory.FactorCertificate.exists_subring_no_monic_factorisation | (intros; apply GlobalTheory.FactorCertificate.exists_subring_no_monic_factorisation <;> assumption)
