import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff ComplexConjugate

namespace GlobalTheory.TorsionForm

def str {m g : ℕ} (K : Ext (m + g) →L[ℂ] Ext (m + g)) : Ext m := fun S =>
  ∑ I : Finset (Fin g), (-1) ^ I.card * K (Pi.single (join ∅ I) 1) (join S I)

def baseMul {n : ℕ} (k : Matrix (Fin n) (Fin n) ℂ) (w : Ext (n + n)) : Ext (n + n) :=
  ∑ i, ∑ l, k i l • wedge (i.castAdd n) (wedge (l.natAdd n) w)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}
  (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ)
  (h : Pt E g → ℝ) (β : Fin n → E)

def IsHeatTraceWith (b : E) (k : Matrix (Fin n) (Fin n) ℂ) (F : ℝ → Ext (n + n)) : Prop :=
  ∃ D : Set (Fl g), IsAddFundamentalDomain M D volume ∧ ∀ u > 0, ∃ K,
    IsHeatKernel τ M j h β b u D K ∧
      F u = phi (∫ x in D, (strN (K 1 (per (τ b) x) (per (τ b) x)) +
        ((u : ℂ)⁻¹) • baseMul k (str (K 1 (per (τ b) x) (per (τ b) x)))))

def IsTorsionFormWith (b : E) (k : Matrix (Fin n) (Fin n) ℂ) (T : Ext (n + n)) : Prop :=
  ∃ F, IsHeatTraceWith τ M j h β b k F ∧ ∀ S, IsMellinDeriv (fun u => F u S) (T S)

def IsClosedHerm (B : Set E) (k : E → E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ) : Prop :=
  (∀ v w, ContDiffOn ℝ ∞ (fun b => k b v w) B) ∧ ∀ b ∈ B, (∀ v w, k b w v = conj (k b v w)) ∧
    ∀ u v w, d10 (fun x => k x v w) b u = d10 (fun x => k x u w) b v

theorem isTorsionFormWith_zero (b : E) (T : Ext (n + n)) :
    IsTorsionFormWith τ M j h β b 0 T ↔ IsTorsionForm τ M j h β b T := by
  simp [IsTorsionFormWith, IsTorsionForm, IsHeatTraceWith, IsHeatTrace, baseMul]

example (k : ℂ) : baseMul (n := 1) (of fun _ _ => k) (Pi.single ∅ 1) Finset.univ = k := by
  have e₁ : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have e₄ : (({1} : Finset (Fin 2)).filter (· = 0)).card = 0 := by decide
  have e₅ : Fin.castAdd 1 (0 : Fin 1) = (0 : Fin 2) := rfl
  have e₆ : Fin.natAdd 1 (0 : Fin 1) = (1 : Fin 2) := rfl
  simp [baseMul, wedge, sgn, e₁, e₄, e₅, e₆]

end GlobalTheory.TorsionForm
