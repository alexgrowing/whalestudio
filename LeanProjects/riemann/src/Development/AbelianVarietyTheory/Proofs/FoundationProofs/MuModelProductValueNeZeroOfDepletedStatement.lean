import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MuModelProductValueNeZeroOfDepleted
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.muModelProduct_value_ne_zero_of_depleted : ∀ (e N l : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (g : ℕ → ℂ) (α β : ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ e → 0 < N → l.Prime → ¬ l ∣ N → Prim (2 * e + 1) N χ⁻¹ (fun n => conj (g n)) → α + β = χ l * conj (g l) → α * β = χ l * (l : ℂ) ^ (2 * e) → α ≠ 0 → θ (-1) = (-1) ^ e * ψ (-1) → θ * χ⁻¹ ≠ 1 → ∀ (B : ℕ) (c : ℕ → ℂ), EigF (2 * e + 1) N l χ (fun q => χ q * conj (g q)) α B c → val B c l α 1 (Zs (2 * e + 1) l (ch θ) (hat ⇑(θ * χ⁻¹)) (fun x y => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e)) ≠ 0 → ∀ (B' : ℕ) (c' : ℕ → ℂ), (∀ a a', MF (2 * e + 1) (N * l) (ch χ⁻¹) a → MF (2 * e + 1) (N * l) (ch χ) a' → qs a' = slz (2 * e + 1) !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) → lam B' c' a = lam B c a') → (∀ a, MF (2 * e + 1) (N * l) (ch χ⁻¹) a → lam B' c' (Uo l a) = χ⁻¹ l * α * lam B' c' a) → val B' c' l (χ⁻¹ l * α) 1 (Zm (2 * e + 1) l (hat θ) (ch (θ * χ⁻¹)) (fun A d => ψ A * ψ⁻¹ d * ((d : ℂ) / A) ^ e)) ≠ 0 := by
  first | exact @GlobalTheory.zm_val_ne_zero | exact GlobalTheory.zm_val_ne_zero | (intros; apply GlobalTheory.zm_val_ne_zero <;> assumption)
