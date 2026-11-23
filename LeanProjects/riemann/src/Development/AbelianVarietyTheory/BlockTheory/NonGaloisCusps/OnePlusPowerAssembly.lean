import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam

section Ring
variable (k : Type) [Field k] (l : ℕ) [Fact l.Prime] [CharP k l]

def onePlusPow (z : ℤ_[l]) : k⟦X⟧ :=
  PowerSeries.map ((ZMod.castHom (dvd_refl l) k).comp PadicInt.toZMod) (PowerSeries.binomialSeries ℤ_[l] z)

def deltaPi (z : ℤ_[l]) (b : k⟦X⟧) : k⟦X⟧ := b.subst (onePlusPow k l z - 1)

def gammaPi (b : k⟦X⟧) : k⟦X⟧ := b.subst (((1 : k⟦X⟧) + PowerSeries.X) ^ (1 + l) - 1)

def phiPi : k⸨X⸩ →+* k⸨X⸩ :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft (l : ℤ))
    (fun _ _ h => mul_left_cancel₀ (by exact_mod_cast (Fact.out : l.Prime).ne_zero) h)
    (fun _ _ => mul_le_mul_iff_right₀ (by exact_mod_cast (Fact.out : l.Prime).pos))

def assemble (y : Fin l → k⸨X⸩) : k⸨X⸩ := ∑ j : Fin l, (1 + vv k) ^ (j : ℕ) * phiPi k l (y j)

variable {k l}

def IsCyclotomic (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) : Prop :=
  (∃ u : (k⟦X⟧)ˣ, ι (vv k) = ((u : k⟦X⟧) : k⸨X⸩) * vv k ^ (l - 1)) ∧
  (∀ a : k⟦X⟧, ∃ b : k⟦X⟧, ι (a : k⸨X⸩) = (b : k⸨X⸩)) ∧
  (∀ b : k⟦X⟧, (∀ z : ℤ_[l], z ^ (l - 1) = 1 → deltaPi k l z b = b) ↔
    ∃ a : k⟦X⟧, ι (a : k⸨X⸩) = (b : k⸨X⸩)) ∧
  (∀ x : k⸨X⸩, ι (R.φ x) = phiPi k l (ι x)) ∧
  (∀ a b : k⟦X⟧, ι (a : k⸨X⸩) = (b : k⸨X⸩) → ι (R.γ (a : k⸨X⸩)) = ((gammaPi k l b : k⟦X⟧) : k⸨X⸩))

def IsPsi (l : ℕ) [Fact l.Prime] (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (ψ : k⸨X⸩ →ₗ[k] k⸨X⸩) : Prop :=
  ∀ (x : k⸨X⸩) (y : Fin l → k⸨X⸩), ι x = assemble k l y → ι (ψ x) = y 0

def PsiRing (R : RingPG k l) (ψ : k⸨X⸩ →ₗ[k] k⸨X⸩) : Prop :=
  (∀ a x, ψ (R.φ a * x) = a * ψ x) ∧ (∀ a, ψ (R.φ a) = a) ∧ (∀ x, ψ (R.γ x) = R.γ (ψ x)) ∧
  ∀ a : ℤ, 2 - (l : ℤ) ≤ a → a ≤ 1 →
    ψ '' {x | ∃ b : k⟦X⟧, x = vv k ^ a * (b : k⸨X⸩)} = {x | ∃ b : k⟦X⟧, x = (b : k⸨X⸩)}

end Ring

section Mod
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

def kerPsi (Ψ : V →ₗ[k] V) (M : Submodule k⟦X⟧ V) (a : ℤ) : Set V := {x | x ∈ sh a M ∧ Ψ x = 0}

def PsiMod (l : ℕ) (ψ : k⸨X⸩ →ₗ[k] k⸨X⸩) (f g₀ g Ψ : V →ₗ[k] V) : Prop :=
  (∀ (a : k⸨X⸩) (x : V), Ψ (a • f x) = ψ a • x) ∧
  (∀ x, Ψ (g x) = g₀ (Ψ x)) ∧
  ∀ M₀ : Submodule k⟦X⟧ V, IsLat M₀ →
    (∀ a : ℤ, 2 - (l : ℤ) ≤ a → a ≤ 1 → Ψ '' (sh a (pull f M₀) : Set V) = (M₀ : Set V)) ∧
    (CondC g₀ M₀ → ∀ a : ℤ, 2 - (l : ℤ) ≤ a → a ≤ 0 →
      (fun x => g x - x) '' kerPsi Ψ (pull f M₀) a = kerPsi Ψ (pull f M₀) (a + 1))

end Mod

def LemmaPsi : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l], 5 ≤ l →
  ∀ (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩), IsCyclotomic R ι →
    Function.Bijective (assemble k l) ∧
    ∃ ψ : k⸨X⸩ →ₗ[k] k⸨X⸩, IsPsi l ι ψ ∧ PsiRing R ψ ∧
      ∀ (V : Type) [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
        [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
        [FiniteDimensional k⸨X⸩ V] (f g₀ g : V →ₗ[k] V),
        Semi R.φ f → Submodule.span k⸨X⸩ (Set.range f) = ⊤ → Semi R.γ g₀ → Semi R.γ g →
        (∀ x, f (g₀ x) = g (f x)) →
        ∃ Ψ : V →ₗ[k] V, PsiMod l ψ f g₀ g Ψ

def CyclotomicExists : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l], 5 ≤ l →
    ∃ (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩), IsCyclotomic R ι

theorem LemmaPsi.modPG (h : LemmaPsi) (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (hl : 5 ≤ l)
    (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (hι : IsCyclotomic R ι) :
    ∃ ψ : k⸨X⸩ →ₗ[k] k⸨X⸩, IsPsi l ι ψ ∧ PsiRing R ψ ∧
      ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
        [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
        [FiniteDimensional k⸨X⸩ V] (D : ModPG R n V) (i : ZMod n),
        ∃ Ψ : V →ₗ[k] V, PsiMod l ψ (D.φ i) (D.γ (i - 1)) (D.γ i) Ψ := by
  obtain ⟨-, ψ, h1, h2, h3⟩ := h l k hl R ι hι
  refine ⟨ψ, h1, h2, fun n V _ _ _ _ _ _ _ _ D i => ?_⟩
  exact h3 V _ _ _ (D.φ_semi i) (D.etale i) (D.γ_semi _) (D.γ_semi _) (D.comm i)

theorem phiPi_vv (k : Type) [Field k] (l : ℕ) [Fact l.Prime] : phiPi k l (vv k) = vv k ^ l := by
  unfold phiPi vv
  erw [HahnSeries.embDomainRingHom_apply, HahnSeries.embDomain_single]
  simp [HahnSeries.single_pow]

end GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters
