import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace GlobalTheory.Whittaker

section Generic

variable {R : Type} [CommRing R] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def superDiag (g : GL (Fin n) R) : R :=
  ∑ i : Fin n, ∑ j : Fin n with j.val = i.val + 1, (g : Matrix (Fin n) (Fin n) R) i j

def IsFunctional (ψ : AddChar R Circle) (π : Representation ℂ (GL (Fin n) R) V) (l : Module.Dual ℂ V) : Prop :=
  ∀ u ∈ unipB R (Fin n), ∀ v, l (π u v) = (ψ (superDiag u) : ℂ) * l v

def IsGeneric (ψ : AddChar R Circle) (π : Representation ℂ (GL (Fin n) R) V) : Prop :=
  ∃ l : Module.Dual ℂ V, l ≠ 0 ∧ IsFunctional ψ π l

end Generic

end GlobalTheory.Whittaker

namespace GlobalTheory.Published

open GlobalTheory.Whittaker

def JacquetShalikaLocalBound : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
      (α : Fin n → ℂˣ), HasSatake π α → IsUnitarisable π → IsGeneric ψ π →
      ∀ i, (resCard k : ℝ) ^ (-(1 / 2) : ℝ) < ‖(α i : ℂ)‖ ∧ ‖(α i : ℂ)‖ < (resCard k : ℝ) ^ (1 / 2 : ℝ)

namespace JacquetShalikaLocalBound

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_uniformizer : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
  exact ⟨Units.mk0 x (by rintro rfl; exact uniformizer_ne_zero (R := k) (by simpa using hx.symm)), hx⟩

end JacquetShalikaLocalBound

end GlobalTheory.Published
