import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusBinomialReduction
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

section Rings
variable {k : Type} [Field k]

def substL (f : k⟦X⟧) (x : k⸨X⸩) : k⸨X⸩ :=
  (f : k⸨X⸩) ^ x.order * ((PowerSeries.subst f (LaurentSeries.powerSeriesPart x) : k⟦X⟧) : k⸨X⸩)

variable (k) (l : ℕ) [Fact l.Prime] [CharP k l]

def red : ℤ_[l] →+* k := (ZMod.castHom (dvd_refl l) k).comp PadicInt.toZMod

def binomPow (t : ℤ_[l]) : k⟦X⟧ := PowerSeries.map (red k l) (PowerSeries.binomialSeries ℤ_[l] t)

def frobπ (x : k⸨X⸩) : k⸨X⸩ := substL ((PowerSeries.X : k⟦X⟧) ^ l) x

def gamπ (x : k⸨X⸩) : k⸨X⸩ := substL ((1 + PowerSeries.X : k⟦X⟧) ^ (1 + l) - 1) x

def actπ (t : ℤ_[l]ˣ) (x : k⸨X⸩) : k⸨X⸩ := substL (binomPow k l t - 1) x

def DeltaInv (x : k⸨X⸩) : Prop := ∀ t : ℤ_[l]ˣ, t ^ (l - 1) = 1 → actπ k l t x = x

variable {k l}

def IsCyclotomic (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) : Prop :=
  Set.range ι = {y | DeltaInv k l y} ∧
  Set.range (fun a : k⟦X⟧ => ι (a : k⸨X⸩)) = {y | (∃ b : k⟦X⟧, y = (b : k⸨X⸩)) ∧ DeltaInv k l y} ∧
  (∃ u : (k⟦X⟧)ˣ, ι (vv k) = ((u : k⟦X⟧) : k⸨X⸩) * vv k ^ (l - 1)) ∧
  (∀ x, ι (R.φ x) = frobπ k l (ι x)) ∧
  (∀ x, ι (R.γ x) = gamπ k l (ι x))

def IsPsi (l : ℕ) [Fact l.Prime] [CharP k l] (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (ψ₀ : k⸨X⸩ →ₗ[k] k⸨X⸩) : Prop :=
  ∀ (a : k⸨X⸩) (x : ℕ → k⸨X⸩),
    ι a = ∑ j ∈ Finset.range l, (1 + vv k) ^ j * frobπ k l (x j) → ι (ψ₀ a) = x 0

def PsiRing (R : RingPG k l) (ψ₀ : k⸨X⸩ →ₗ[k] k⸨X⸩) : Prop :=
  (∀ a b, ψ₀ (R.φ a * b) = a * ψ₀ b) ∧ ψ₀ 1 = 1 ∧ (∀ a, ψ₀ (R.γ a) = R.γ (ψ₀ a)) ∧
  ∀ a : ℤ, 2 - (l : ℤ) ≤ a → a ≤ 1 →
    ψ₀ '' {x | ∃ b : k⟦X⟧, x = vv k ^ a * (b : k⸨X⸩)} = Set.range (fun b : k⟦X⟧ => (b : k⸨X⸩))

end Rings

section Modules
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

def kerPsi (ψ : V →ₗ[k] V) (M : Submodule k⟦X⟧ V) (a : ℤ) : Set V := {x | x ∈ sh a M ∧ ψ x = 0}

def PsiShift (l : ℕ) (g ψ : V →ₗ[k] V) (M : Submodule k⟦X⟧ V) : Prop :=
  ∀ a : ℤ, 2 - (l : ℤ) ≤ a → a ≤ 0 → (fun x => g x - x) '' kerPsi ψ M a = kerPsi ψ M (a + 1)

end Modules

def LemmaPsi : Prop :=
  ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l], 5 ≤ l →
  ∀ (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩), IsCyclotomic R ι →
  ∃ ψ₀ : k⸨X⸩ →ₗ[k] k⸨X⸩, IsPsi l ι ψ₀ ∧ PsiRing R ψ₀ ∧
    ∀ {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
      [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
      [FiniteDimensional k⸨X⸩ V] (D : ModPG R n V),
      ∃ ψ : ZMod n → V →ₗ[k] V,
        (∀ i a x, ψ i (a • D.φ i x) = ψ₀ a • x) ∧
        (∀ i x, ψ i (D.γ i x) = D.γ (i - 1) (ψ i x)) ∧
        ∀ (i : ZMod n) (M₀ : Submodule k⟦X⟧ V), IsLat M₀ → CondC (D.γ (i - 1)) M₀ →
          PsiShift l (D.γ i) (ψ i) (pull (D.φ i) M₀)

def LemmaPsiStep : Prop :=
  ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l], 5 ≤ l →
  ∀ (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩), IsCyclotomic R ι →
  ∃ ψ₀ : k⸨X⸩ →ₗ[k] k⸨X⸩, IsPsi l ι ψ₀ ∧ PsiRing R ψ₀ ∧
    ∀ {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
      [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
      [FiniteDimensional k⸨X⸩ V] (f g₀ g₁ : V →ₗ[k] V),
      Semi R.φ f → Submodule.span k⸨X⸩ (Set.range f) = ⊤ → Semi R.γ g₀ → Semi R.γ g₁ →
      (∀ x, f (g₀ x) = g₁ (f x)) →
      ∃ ψ : V →ₗ[k] V,
        (∀ a x, ψ (a • f x) = ψ₀ a • x) ∧ (∀ x, ψ (g₁ x) = g₀ (ψ x)) ∧
        ∀ M₀ : Submodule k⟦X⟧ V, IsLat M₀ → CondC g₀ M₀ → PsiShift l g₁ ψ (pull f M₀)

def CyclotomicExists : Prop :=
  ∀ (k : Type) [Field k] (l : ℕ) [Fact l.Prime] [CharP k l], 5 ≤ l →
    ∃ (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩), IsCyclotomic R ι

theorem binomPow_natCast (k : Type) [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (m : ℕ) :
    binomPow k l (m : ℤ_[l]) = (1 + PowerSeries.X) ^ m := by
  rw [binomPow, PowerSeries.binomialSeries_nat]
  simp

end GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusBinomialReduction
