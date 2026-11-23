import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation

set_option autoImplicit false

noncomputable section

open NumberField

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

variable {V : Type} [AddCommGroup V] [Module ℚ V]

def coneOn (s : Finset V) : Set V :=
  {x | ∃ t : V → ℚ, (∀ i ∈ s, 0 < t i) ∧ x = ∑ i ∈ s, t i • i}

def SignConst (l : V →ₗ[ℚ] ℚ) (C : Set V) : Prop :=
  (∀ x ∈ C, l x = 0) ∨ (∀ x ∈ C, 0 < l x) ∨ (∀ x ∈ C, l x < 0)

inductive Tile (P : Set V) (Q : Set V → Prop) : Set V → Prop
  | empty : Tile P Q ∅
  | cone (s : Finset V) (hli : LinearIndepOn ℚ id (s : Set V)) (hP : (s : Set V) ⊆ P) (hQ : Q (coneOn s)) :
      Tile P Q (coneOn s)
  | union {A B : Set V} (hA : Tile P Q A) (hB : Tile P Q B) (hAB : Disjoint A B) : Tile P Q (A ∪ B)

theorem tile_ray (P : Set V) (v : V) (hv : v ≠ 0) (hP : v ∈ P) : Tile P (fun _ => True) (coneOn {v}) :=
  Tile.cone {v} (by simpa using LinearIndepOn.singleton (R := ℚ) (v := id) (i := v) (by simpa using hv)) (by simpa using hP) trivial

def posCone (F : Type) [Field F] [NumberField F] : ConvexCone ℚ F where
  carrier := {x | TotPos F x}
  smul_mem' := by
    intro c hc x hx σ
    have h : σ (c • x) = (c : ℝ) * σ x := by
      rw [Rat.smul_def, map_mul, map_ratCast]
    rw [h]
    exact mul_pos (by exact_mod_cast hc) (hx σ)
  add_mem' := by
    intro x hx y hy σ
    rw [map_add]
    exact add_pos (hx σ) (hy σ)

def congSubgroup {F : Type} [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)) : Subgroup (𝓞 F)ˣ where
  carrier := congUnits 𝔣
  mul_mem' := by
    intro a b ha hb
    refine ⟨?_, fun σ => ?_⟩
    · have h : ((a * b : (𝓞 F)ˣ) : 𝓞 F) - 1 = (a : 𝓞 F) * ((b : 𝓞 F) - 1) + ((a : 𝓞 F) - 1) := by
        rw [Units.val_mul]; ring
      rw [h]
      exact 𝔣.add_mem (𝔣.mul_mem_left _ hb.1) ha.1
    · have h : (((a * b : (𝓞 F)ˣ) : 𝓞 F) : F) = ((a : 𝓞 F) : F) * ((b : 𝓞 F) : F) := by
        rw [Units.val_mul]; simp
      rw [h, map_mul]
      exact mul_pos (ha.2 σ) (hb.2 σ)
  one_mem' := by
    refine ⟨by simp, fun σ => ?_⟩
    simp
  inv_mem' := by
    intro a ha
    refine ⟨?_, fun σ => ?_⟩
    · have h : ((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) - 1 = -(((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * ((a : 𝓞 F) - 1)) := by
        have : ((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * (a : 𝓞 F) = 1 := by simp
        linear_combination this
      rw [h]
      exact 𝔣.neg_mem (𝔣.mul_mem_left _ ha.1)
    · have h1 : (((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ((a : 𝓞 F) : F) = 1 := by
        have : ((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * (a : 𝓞 F) = 1 := by simp
        exact_mod_cast congrArg (fun z : 𝓞 F => (z : F)) this
      have h2 := congrArg σ h1
      rw [map_mul, map_one] at h2
      have h3 := ha.2 σ
      by_contra hn
      have : σ (((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * σ ((a : 𝓞 F) : F) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hn) h3.le
      linarith

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
