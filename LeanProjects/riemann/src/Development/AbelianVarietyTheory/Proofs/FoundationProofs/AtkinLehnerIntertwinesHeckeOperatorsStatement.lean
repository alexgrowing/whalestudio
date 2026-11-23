import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerIntertwinesHeckeOperators
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atkinLehner_intertwines_hecke_operators : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (a a' : ℕ → ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → MF k (N * l) (ch χ) a → MF k (N * l) (ch χ⁻¹) a' → qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) → (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs (To k (ch χ q) q a)) = (ch χ q : ℂ) • qs (To k (ch χ⁻¹ q) q a')) ∧ slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs (Uo l a)) = (ch χ l : ℂ) • qs (Uo l a') := by
  first | exact @GlobalTheory.EisM.AtkinLehner.alHecke | exact GlobalTheory.EisM.AtkinLehner.alHecke | (intros; apply GlobalTheory.EisM.AtkinLehner.alHecke <;> assumption)
