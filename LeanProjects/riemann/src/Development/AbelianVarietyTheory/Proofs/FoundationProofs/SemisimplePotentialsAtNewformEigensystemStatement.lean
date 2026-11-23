import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SemisimplePotentialsAtNewformEigensystem
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semisimple_potentials_at_newform_eigensystem : ∀ (k : ℕ) (g : UpperTheory.V.Af.Newform k) (N l : ℕ) (hN : g.M ∣ N), 5 ≤ N → l.Prime → ¬ l ∣ N → Odd k → 3 ≤ k → ∀ α : ℂ, α ^ 2 - g.a l * α + g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) = 0 → α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) → α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 2) → ∀ lam : Letter → ℂ, (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → lam (Letter.T q) = g.a q) → lam Letter.U = α → (∀ d : ℕ, Nat.Coprime d N → lam (Letter.D d) = g.χ (d : ZMod g.M)) → SSPotB N l (k - 2) lam := by
  first | exact @GlobalTheory.KZ.SSPotBr.ssPotB_at_newform | exact GlobalTheory.KZ.SSPotBr.ssPotB_at_newform | (intros; apply GlobalTheory.KZ.SSPotBr.ssPotB_at_newform <;> assumption)
