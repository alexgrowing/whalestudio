import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatExtensionRegularSequence
import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open ReciprocityTheory.AnForm.R.FinalTheorems
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_extension_regular_sequence : ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] (φ : A →+* B) [IsLocalHom φ], φ.Flat → IsRegularLocalRing (B ⧸ (IsLocalRing.maximalIdeal A).map φ) → ∀ (n : ℕ) (r : Fin n → A), Rsp A n r → ∃ (g : ℕ) (s : Fin g → B), Rsp B (n + g) (Fin.append (fun i => φ (r i)) s) := by
  first | exact @GlobalTheory.rsp_append_of_flat_of_isRegularLocalRing_closedFibre | exact GlobalTheory.rsp_append_of_flat_of_isRegularLocalRing_closedFibre | (intros; apply GlobalTheory.rsp_append_of_flat_of_isRegularLocalRing_closedFibre <;> assumption)
