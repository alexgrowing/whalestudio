import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedEisensteinProductValueNeZeroOfRankin
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depletedEisensteinProduct_value_ne_zero_of_rankin : ∀ (e N l : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (φ : DirichletCharacter ℂ (N * l)) (t : ℕ → ℂ) (α c₀ c₁ : ℂ) (B : ℕ) (c : ℕ → ℂ), 1 ≤ e → 0 < N → l.Prime → ¬ l ∣ N → α ≠ 0 → EigF (2 * e + 1) N l χ⁻¹ t α B c → θ (-1) = (-1) ^ e * ψ (-1) → χ (-1) = -1 → θ * χ ≠ 1 → (∀ d : ℤ, ch φ d = ch (θ * χ) d * ch ψ d) → MF e (N * l) (fun d => ch ψ d * ch θ d) (eis e c₀ (ch ψ) (ch θ)) → MF (e + 1) (N * l) (ch φ⁻¹) (eis (e + 1) c₁ (hat φ) fun _ => 1) → lam B c (mul (eis e c₀ (ch ψ) (ch θ)) (eis (e + 1) c₁ (hat φ) fun _ => 1)) ≠ 0 → α ≠ θ l → α ≠ (l : ℂ) ^ e * χ⁻¹ l → val B c l α 1 (Zs (2 * e + 1) l (ch θ) (hat ⇑(θ * χ)) (fun x y => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e)) ≠ 0 := by
  first | exact @GlobalTheory.EisM.val_depleted_ne_zero | exact GlobalTheory.EisM.val_depleted_ne_zero | (intros; apply GlobalTheory.EisM.val_depleted_ne_zero <;> assumption)
