import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv

noncomputable section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapOrb

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def IsModelMap (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K)
    (u x : B.A) {n : ℕ} (γ : GLw n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) : Prop :=
  (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) ∧ (∀ y, ψ (u * y) = γ.val *ᵥ ψ y) ∧
    ∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z)

theorem isModel_iff (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K)
    (u x : B.A) {n : ℕ} (γ : GLw n w) : IsModel w e B u x γ ↔ ∃ ψ, IsModelMap w e B u x γ ψ := Iff.rfl

def pullLat (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) {n : ℕ}
    (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (g : GLw n w) : Submodule K.O B.A where
  carrier := {y | ∀ (c : K.O) (i : Fin n), ((g⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E}
  zero_mem' := by
    intro c i
    simp
  add_mem' := by
    intro a b ha hb c i
    rw [smul_add, map_add, Matrix.mulVec_add, Pi.add_apply]
    exact add_mem (ha c i) (hb c i)
  smul_mem' := by
    intro c' a ha c i
    rw [smul_smul]
    exact ha (c * c') i

def torusOf (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) {n : ℕ}
    (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (g : GLw n w) : B.Aˣ :=
  if h : ∃ a : B.Aˣ, ∀ y, ψ ((a : B.A) * y) = g.val *ᵥ ψ y then h.choose else 1

theorem torusOf_spec (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) {n : ℕ}
    (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (g : GLw n w) (a : B.Aˣ)
    (ha : ∀ y, ψ ((a : B.A) * y) = g.val *ᵥ ψ y) : torusOf w B ψ g = a := by
  have h : ∃ a : B.Aˣ, ∀ y, ψ ((a : B.A) * y) = g.val *ᵥ ψ y := ⟨a, ha⟩
  unfold torusOf
  rw [dif_pos h]
  apply Units.ext
  have h1 := h.choose_spec 1
  have h2 := ha 1
  rw [mul_one] at h1 h2
  exact ψ.injective (h1.trans h2.symm)

end GlobalTheory.KapOrb
