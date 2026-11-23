import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LogFactorialIndices.StatementSize

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PaddedWittNormSquare

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker

def padZero {a : ℕ} (b : ℕ) (ν : DomWeight a) : Fin b → ℤ :=
  fun i => if h : i.1 < a then ν.w ⟨i.1, h⟩ else 0

def IsStepWeight {a b : ℕ} (lam ν : DomWeight a) (lam' : DomWeight b) (s' s : ℤ) : Prop :=
  (∀ i, ν.w i = lam.w i + s') ∧ (∀ i, 0 ≤ ν.w i) ∧ (∀ i, lam'.w i + s = padZero b ν i)

def wtSize {a : ℕ} (ν : DomWeight a) : ℕ := ∑ i, (ν.w i).toNat

def lastEntry {a : ℕ} (ν : DomWeight a) : ℕ := ν.detShift.toNat

def normSq {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (v : VV ℂ lam) : ℝ :=
  (pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) v v).re

def OpNormSqLe {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (t : ℝ) : Prop :=
  ∀ v : VV ℂ lam, normSq lam' (T v) ≤ t * normSq lam v

def unitNormSq {ι : Type} [Fintype ι] {a b : ℕ} (r : ι → ℝ) (z : VCx ι a b) : ℝ :=
  ∑ τ, ∑ β, ∑ α, ‖(r τ : ℂ) * z τ β α‖ ^ 2

def tmax {ι : Type} [Fintype ι] {a : ℕ} (b : ℕ) (ν : ι → DomWeight a) (Om : ι → ℝ) (S : ℝ) : ℝ :=
  S ^ 2 * ∏ τ, ((Om τ)⁻¹ ^ wtSize (ν τ) * Real.exp 1 * (2 * (wtSize (ν τ) : ℝ) + 2) ^ (2 * (a * b)) *
    Real.exp (∑ i, Formalism.LatticeIndexTer.ph ((ν τ).w i : ℝ)))

def BlockBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (a b : ℕ), a ≤ b →
  ∀ (lam ν : ι → DomWeight a) (lam' : ι → DomWeight b) (s' s : ι → ℤ),
    (∀ τ, IsStepWeight (lam τ) (ν τ) (lam' τ) (s' τ) (s τ)) →
    (∀ τ, a < b ∨ lastEntry (ν τ) = 0) →
  ∀ (G : VCx ι a b → ℂ) (S : ℝ) (r Om : ι → ℝ) (cD : ι → ℂ),
    Differentiable ℂ G →
    (∀ τ, 0 < r τ) →
    (∀ z, ‖G z‖ ≤ S * Real.exp (unitNormSq r z / 2)) →
    (∀ τ, 0 < Om τ) →
    (∀ τ, ‖cD τ * (r τ : ℂ)‖ ^ 2 = 1 / Om τ) →
    OpNormSqLe lam lam' (jetOp lam lam' (jetC cD G) fun τ => lastEntry (ν τ)) (tmax b ν Om S)

example : Formalism.LatticeIndexTer.ph 0 = 0 := by simp [Formalism.LatticeIndexTer.ph]

theorem natW_eq_padZero {a b : ℕ} (hab : a ≤ b) {lam ν : DomWeight a} {lam' : DomWeight b} {s' s : ℤ}
    (h : IsStepWeight lam ν lam' s' s) (hg : a < b ∨ lastEntry ν = 0) (i : Fin b) :
    ((lam'.natW i : ℕ) : ℤ) = padZero b ν i := by
  obtain ⟨h1, h2, h3⟩ := h
  have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le _) i.2
  have hpad : ∀ j, 0 ≤ padZero b ν j := by
    intro j
    unfold padZero
    split_ifs
    · exact h2 _
    · exact le_rfl
  let j0 : Fin b := ⟨b - 1, by omega⟩
  have hlast : padZero b ν j0 = 0 := by
    unfold padZero
    split_ifs with hlt
    · have hlt' : b - 1 < a := hlt
      rcases hg with hg | hg
      · omega
      · have ha : 0 < a := by omega
        have hz : ν.w ⟨a - 1, by omega⟩ ≤ 0 := by
          unfold lastEntry DomWeight.detShift at hg
          rw [dif_pos ha] at hg
          exact Int.toNat_eq_zero.mp hg
        have hidx : (⟨j0.1, hlt⟩ : Fin a) = ⟨a - 1, by omega⟩ := Fin.ext (by simp [j0]; omega)
        rw [hidx]
        exact le_antisymm hz (h2 _)
    · rfl
  have hshift : lam'.detShift = -s := by
    unfold DomWeight.detShift
    rw [dif_pos hb]
    show lam'.w j0 = -s
    have h30 := h3 j0
    rw [hlast] at h30
    linarith
  unfold DomWeight.natW
  rw [hshift]
  have hw : lam'.w i - -s = padZero b ν i := by linarith [h3 i]
  rw [hw, Int.toNat_of_nonneg (hpad i)]

example : ∃ (lam ν : DomWeight 1) (lam' : DomWeight 2) (s' s : ℤ),
    IsStepWeight lam ν lam' s' s ∧ lastEntry ν = 3 ∧ wtSize ν = 3 := by
  refine ⟨⟨fun _ => 0, fun _ _ _ => le_rfl⟩, ⟨fun _ => 3, fun _ _ _ => le_rfl⟩,
    ⟨![2, -1], by decide⟩, 3, 1, ⟨fun _ => rfl, fun _ => by simp, ?_⟩, rfl, rfl⟩
  intro i
  fin_cases i <;> rfl

example (z : VCx Unit 1 2) : ‖z () 0 0‖ ≤ 1 * Real.exp (unitNormSq (fun _ => 1) z / 2) := by
  have h1 : ‖z () 0 0‖ ^ 2 ≤ unitNormSq (fun _ => 1) z := by
    simp only [unitNormSq, Finset.univ_unique, Finset.sum_singleton, Fin.sum_univ_two, Complex.ofReal_one, one_mul]
    have := sq_nonneg ‖z () 1 0‖
    simpa using this
  have h2 := Real.add_one_le_exp (unitNormSq (fun _ => (1 : ℝ)) z / 2)
  nlinarith [sq_nonneg (‖z () 0 0‖ - 1)]

end GlobalTheory.IndefiniteRowSideFullHecke.PaddedWittNormSquare
