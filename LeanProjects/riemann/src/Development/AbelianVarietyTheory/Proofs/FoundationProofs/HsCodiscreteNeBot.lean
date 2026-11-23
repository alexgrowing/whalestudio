import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.KZ.BettiB

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def BtN (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (n : ℕ) (b : X.Fn l)
    (c : Gam N l → MvPolynomial (Fin 2) (ZMod (l ^ n))) : Prop :=
  ∀ u : Fin 2 → ℤ_[l], ∃ χ : SL(2, ℤ) → ZMod (l ^ n), H3.Kum X l n (b u) χ ∧ ∃ M : ℕ, 0 < M ∧
    ∀ δ : Gam N l, (δ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma M →
      MvPolynomial.eval (fun i => PadicInt.toZModPow n (u i)) (c δ) = χ δ

def BtZ (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (b : X.Fn l) (c : Gam N l → MvPolynomial (Fin 2) ℤ_[l]) : Prop :=
  ∀ n : ℕ, BtN X N l n b (fun δ => MvPolynomial.map (PadicInt.toZModPow n) (c δ))

def Z1 (N l w : ℕ) [Fact l.Prime] : Submodule ℤ_[l] (Gam N l → MvPolynomial (Fin 2) ℤ_[l]) where
  carrier := {c | (∀ γ, (c γ).IsHomogeneous w) ∧
    ∀ γ δ : Gam N l, c (γ * δ) = slP ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (c γ) + c δ}
  add_mem' := by
    rintro c c' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun γ => (h1 γ).add (h1' γ), fun γ δ => ?_⟩
    simp only [Pi.add_apply, h2, h2', map_add]; abel
  zero_mem' := ⟨fun γ => MvPolynomial.isHomogeneous_zero _ _ _, fun γ δ => by simp⟩
  smul_mem' := by
    rintro r c ⟨h1, h2⟩
    refine ⟨fun γ => ?_, fun γ δ => ?_⟩
    · simpa [MvPolynomial.smul_eq_C_mul] using (MvPolynomial.isHomogeneous_C _ r).mul (h1 γ)
    · simp only [Pi.smul_apply, h2, map_smul, smul_add]

theorem hs_codiscrete_neBot : (Filter.codiscreteWithin Hs).NeBot := by
  rw [Filter.neBot_iff]
  intro h
  have hmem : (∅ : Set ℂ) ∈ Filter.codiscreteWithin Hs := by rw [h]; exact Filter.mem_bot
  rw [mem_codiscreteWithin] at hmem
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have hd := hmem Complex.I hI
  simp only [Set.diff_empty] at hd
  have hopen : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im
  have hle : nhdsWithin Complex.I {Complex.I}ᶜ ≤ Filter.principal Hs :=
    le_trans nhdsWithin_le_nhds (Filter.le_principal_iff.2 (hopen.mem_nhds hI))
  have hbot : nhdsWithin Complex.I {Complex.I}ᶜ = ⊥ := by
    have := hd.mono_right hle
    exact disjoint_self.1 this
  exact (NormedField.nhdsNE_neBot Complex.I).ne hbot

theorem btZ_zero (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] : BtZ X N l 0 0 := by
  intro n u
  refine ⟨0, ⟨1, fun _ => 1, fun _ => 1, 1, one_pos, ?_, ?_, ?_⟩, 1, one_pos, fun δ _ => by simp⟩
  · simp [Tower.cls]
  · apply H3.isRoot_one
    haveI := hs_codiscrete_neBot
    exact one_ne_zero
  · intro δ _ z _; simp

end GlobalTheory.KZ.BettiB
