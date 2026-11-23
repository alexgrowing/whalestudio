import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CochainCoboundaryProdHomIdentities
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eta_one_conj_mul_of_cup_coboundary : ∀ (Γ : Type) [Group Γ] (N : ℕ) (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N),
  (∀ g h, (x g).toAdd * (y h).toAdd = η h - η (g * h) + η g) →
  η 1 = 0 ∧ (∀ g n, η (g * n * g⁻¹) = η n + (x n).toAdd * (y g).toAdd - (x g).toAdd * (y n).toAdd) ∧
  (∀ m n, (x m).toAdd = 0 → η (m * n) = η m + η n) := by
  first | exact @GlobalTheory.cochain_coboundary_prod_hom_identities | exact GlobalTheory.cochain_coboundary_prod_hom_identities | (intros; apply GlobalTheory.cochain_coboundary_prod_hom_identities <;> assumption)
