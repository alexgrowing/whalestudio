import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform

noncomputable section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory.EisM

open UpperTheory.V.Af

def mes (k l : ℕ) {N : ℕ} (θ θ' : DirichletCharacter ℂ N) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (m : ℕ) (f : ZMod (l ^ m) → ℂ) : ℂ :=
  val B c l α m (Zs k l (ch θ) (hat θ') (quo f))

structure Meas {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e : ℕ) {N : ℕ} (θ θ' : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ l) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (v : ℂ) : Prop where
  compat : ∀ m : ℕ, 1 ≤ m → ∀ (f : ZMod (l ^ m) → ℂ) (f' : ZMod (l ^ (m + 1)) → ℂ), (∀ x, f (-x) = θ (-1) * f x) →
    (∀ x : ℕ, f' x = f x) → mes (2 * e + 1) l θ θ' α B c (m + 1) f' = mes (2 * e + 1) l θ θ' α B c m f
  bound : ∃ C : ℝ, ∀ (m : ℕ) (f : ZMod (l ^ m) → ℂ) (δ : ℝ), 0 ≤ δ → (∀ x, ‖ι.symm (f x)‖ ≤ δ) →
    ‖ι.symm (mes (2 * e + 1) l θ θ' α B c m f)‖ ≤ C * δ
  field : ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ ∀ (m : ℕ) (f : ZMod (l ^ m) → ℂ)
    (E' : IntermediateField ℚ_[l] (PadicAlgCl l)), E ≤ E' → (∀ x, ι.symm (f x) ∈ E') → ι.symm (mes (2 * e + 1) l θ θ' α B c m f) ∈ E'
  interp : ∃ C : ℝ, ∀ m : ℕ, 1 ≤ m → ∀ (f : ZMod (l ^ m) → ℂ) (δ : ℝ), 0 ≤ δ → (∀ x, f (-x) = θ (-1) * f x) →
    (∀ x y : ℕ, ¬ l ∣ x → ¬ l ∣ y → ‖ι.symm (quo f x y - ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e)‖ ≤ δ) →
    ‖ι.symm (mes (2 * e + 1) l θ θ' α B c m f - v)‖ ≤ C * δ

def Chapter : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : PadicAlgCl l ≃+* ℂ) (e : ℕ), 1 ≤ e → ∀ g : Newform (2 * e + 1), ¬ l ∣ g.M →
    ‖ι.symm (g.a l)‖ = 1 → ∀ ψ : DirichletCharacter ℂ l,
    ∃ (N : ℕ) (χ θ : DirichletCharacter ℂ N) (α v : ℂ) (B : ℕ) (c : ℕ → ℂ) (c₁ d₁ : ℕ),
      5 ≤ N ∧ g.M ∣ N ∧ ¬ l ∣ N ∧ (∀ d : ℕ, d.Coprime N → χ d = g.χ d) ∧ ‖ι.symm α‖ = 1 ∧
      α ^ 2 - χ⁻¹ l * g.a l * α + χ⁻¹ l * (l : ℂ) ^ (2 * e) = 0 ∧
      EigF (2 * e + 1) N l χ⁻¹ (fun q => χ⁻¹ q * g.a q) α B c ∧
      θ (-1) = (-1) ^ e * ψ (-1) ∧ θ * χ ≠ 1 ∧ χ (-1) = -1 ∧
      Meas ι e θ (θ * χ) ψ α B c v ∧ v ≠ 0 ∧
      1 < c₁ ∧ 1 < d₁ ∧ c₁.Coprime (6 * N * l) ∧ d₁.Coprime (6 * N * l) ∧
      (c₁ : ℂ) ^ e ≠ θ c₁ * ψ⁻¹ c₁ ∧ (d₁ : ℂ) ^ 2 ≠ (d₁ : ℂ) ^ (e + 1) * ((θ * χ)⁻¹ d₁ * ψ⁻¹ d₁)

def Bridge : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (l : ℕ) [Fact l.Prime] (k m n : ℕ) [NeZero (l ^ n)] [NeZero (l ^ m)], 3 ≤ k → Odd k → 1 ≤ m → ∀ (h : m ≤ n)
    (ζ : K), IsPrimitiveRoot ζ (l ^ n) → ∀ ψ : DirichletCharacter K (l ^ m), ψ.IsPrimitive →
    ∀ (b₁ b₂ u v : ℤ → K) (f₁ f₂ : ZMod (l ^ n) → K) (c d : (ZMod (l ^ n))ˣ),
      (∀ x : ℤ, b₁ ((l : ℤ) ^ (n - m) * x) = u x) → (∀ x : ℤ, b₂ ((l : ℤ) ^ (n - m) * x) = v x) →
      (∀ x, u (-x) = ψ (-1) * u x) → (∀ x, v (-x) = -ψ (-1) * v x) → ∀ s : ℕ,
      -((l : K) ^ (n * k) / (l : K) ^ (n * 4)) *
        ∑ γ : ((ZMod (l ^ n))ˣ × (ZMod (l ^ n))ˣ) × ZMod (l ^ n) × ZMod (l ^ n),
          ψ ((((γ.1.1 : ZMod (l ^ n)) * γ.2.2 - (γ.1.2 : ZMod (l ^ n)) * γ.2.1).val : ℕ) : ZMod (l ^ m)) *
            mul (Fser (k - 1) (l ^ n) ζ b₁ (f₁ (c * γ.1.1)) (c * γ.1.1) (c * γ.2.1))
              (Fser 1 (l ^ n) ζ b₂ (f₂ (d * γ.1.2)) (d * γ.1.2) (d * γ.2.2)) s =
      if l ^ n ∣ s then -4 * ((l : K) ^ m)⁻¹ * (∑ a : ZMod (l ^ m), ψ a * ζ ^ (l ^ (n - m) * a.val)) *
        ψ⁻¹ ((((c * d : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val : ℕ) : ZMod (l ^ m)) *
          (Uo l)^[m] (Zs k l u v (quo ψ)) (s / l ^ n) else 0

end GlobalTheory.EisM

end
