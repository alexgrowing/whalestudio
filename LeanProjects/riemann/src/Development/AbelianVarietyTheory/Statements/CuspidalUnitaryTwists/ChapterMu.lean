import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform

noncomputable section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory.EisM

open UpperTheory.V.Af

def Zm {R : Type*} [CommRing R] (k l : ℕ) (u v : ℤ → R) (F : ℕ → ℕ → R) : ℕ → R := fun n =>
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ∑ x ∈ p.1.divisorsAntidiagonal, ∑ y ∈ p.2.divisorsAntidiagonal,
    if l ∣ p.1 ∨ l ∣ p.2 then 0 else (x.1 : R) ^ (k - 2) * u x.1 * v y.1 * F x.1 y.2

def tw1 (N : ℕ) (s : ℂ) (x : ℤ) : ℤ → ℂ := fun A => (if (A : ZMod N) = x then 1 else 0) + s * (if (A : ZMod N) = -x then 1 else 0)

def tw2 (N : ℕ) (s : ℂ) : ℤ → ℂ := fun B => (if (B : ZMod N) = 1 then 1 else 0) - s * (if (B : ZMod N) = -1 then 1 else 0)

def mesMu (k l : ℕ) (u v : ℤ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (m : ℕ) (f : ZMod (l ^ m) → ℂ) : ℂ :=
  val B c l α m (Zm k l u v (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)))

structure EigAll (k N l : ℕ) (χ : DirichletCharacter ℂ N) (t : ℕ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) : Prop extends
    EigF k N l χ t α B c where
  kill : ∀ (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), ε ≠ χ → MF k (N * l) (ch ε) a → lam B c a = 0

structure MeasMu {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e : ℕ) (s : ℂ) (u w : ℤ → ℂ) (ψ : DirichletCharacter ℂ l) (α : ℂ)
    (B : ℕ) (c : ℕ → ℂ) (v : ℂ) : Prop where
  compat : ∀ m : ℕ, 1 ≤ m → ∀ (f : ZMod (l ^ m) → ℂ) (f' : ZMod (l ^ (m + 1)) → ℂ), (∀ y, f (-y) = s * f y) →
    (∀ y : ℕ, f' y = f y) → mesMu (2 * e + 1) l u w α B c (m + 1) f' = mesMu (2 * e + 1) l u w α B c m f
  bound : ∃ C : ℝ, ∀ (m : ℕ) (f : ZMod (l ^ m) → ℂ) (δ : ℝ), 0 ≤ δ → (∀ y, ‖ι.symm (f y)‖ ≤ δ) →
    ‖ι.symm (mesMu (2 * e + 1) l u w α B c m f)‖ ≤ C * δ
  field : ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ ∀ (m : ℕ) (f : ZMod (l ^ m) → ℂ)
    (E' : IntermediateField ℚ_[l] (PadicAlgCl l)), E ≤ E' → (∀ y, ι.symm (f y) ∈ E') → ι.symm (mesMu (2 * e + 1) l u w α B c m f) ∈ E'
  interp : ∃ C : ℝ, ∀ m : ℕ, 1 ≤ m → ∀ (f : ZMod (l ^ m) → ℂ) (δ : ℝ), 0 ≤ δ → (∀ y, f (-y) = s * f y) →
    (∀ a d : ℕ, ¬ l ∣ a → ¬ l ∣ d → ‖ι.symm (f ((a : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹) - ψ a * ψ⁻¹ d * ((d : ℂ) / a) ^ e)‖ ≤ δ) →
    ‖ι.symm (mesMu (2 * e + 1) l u w α B c m f - v)‖ ≤ C * δ

def ChapterMu : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : PadicAlgCl l ≃+* ℂ) (e : ℕ), 1 ≤ e → ∀ g : Newform (2 * e + 1), ¬ l ∣ g.M →
    ‖ι.symm (g.a l)‖ = 1 → ∀ (ψ : DirichletCharacter ℂ l) (N₀ : ℕ), 0 < N₀ → ¬ l ∣ N₀ →
    ∃ (N : ℕ) (χ θ : DirichletCharacter ℂ N) (α v : ℂ) (B : ℕ) (c : ℕ → ℂ) (c₁ d₁ : ℕ),
      5 ≤ N ∧ g.M ∣ N ∧ N₀ ∣ N ∧ ¬ l ∣ N ∧ (∀ d : ℕ, d.Coprime N → χ d = g.χ d) ∧ ‖ι.symm α‖ = 1 ∧
      α ^ 2 - g.a l * α + χ l * (l : ℂ) ^ (2 * e) = 0 ∧
      EigAll (2 * e + 1) N l χ (fun q => g.a q) α B c ∧ χ (-1) = -1 ∧ θ (-1) = (-1) ^ e * ψ (-1) ∧
      MeasMu ι e ((-1) ^ e * ψ (-1)) (ch θ) (tw2 N ((-1) ^ e * ψ (-1))) ψ α B c v ∧ v ≠ 0 ∧
      1 < c₁ ∧ 1 < d₁ ∧ c₁.Coprime (6 * N * l) ∧ d₁.Coprime (6 * N * l) ∧
      (∀ z : ℂ, ‖z‖ = 1 → (c₁ : ℂ) ^ e ≠ z) ∧ ∀ n₁ n₂ : ℤ, (n₁ = 1 ∨ n₁ = -1) → (d₁ : ℂ) ^ 2 ≠ (d₁ : ℂ) ^ (e + 1) * ((θ * χ⁻¹) d₁ ^ n₁ * ψ d₁ ^ n₂)

end GlobalTheory.EisM

end
