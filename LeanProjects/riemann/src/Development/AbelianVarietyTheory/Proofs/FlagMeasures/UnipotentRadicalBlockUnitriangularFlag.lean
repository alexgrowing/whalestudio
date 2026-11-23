import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Dchart
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentUpperFacts

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellDens

private lemma Hpk_apply_of_lt_eq_ite (k r : ℕ) (c s : Fin (2 * r + k + 1)) (hc : c.val < r) :
    Formalism.QuantumDeterminants.Hpk k r c s = if c.val + s.val = 2 * r + k then 1 else 0 := by
  by_cases h : c.val + s.val = 2 * r + k
  · simp [Formalism.QuantumDeterminants.Hpk, hc, h]
  · have h' : ¬ r ≤ c.val := Nat.not_le.mpr hc
    simp [Formalism.QuantumDeterminants.Hpk, h, h']

private lemma Hpk_mul_apply_eq_Hpk_apply_of_lt_val (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hU : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r)
    (hcol : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      g i (Formalism.QuantumDeterminants.eI k r a) = if i = Formalism.QuantumDeterminants.eI k r a then 1 else 0)
    (q : Fin (2 * r + k + 1)) (hq : r + k < q.val) :
    ∀ c : ℕ, ∀ hc : c + q.val ≤ 2 * r + k,
      (Formalism.QuantumDeterminants.Hpk k r * g) ⟨c, by omega⟩ q = Formalism.QuantumDeterminants.Hpk k r ⟨c, by omega⟩ q := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hc
    have hcr : c < r := by omega
    have hE : Formalism.QuantumDeterminants.eI k r ⟨c, hcr⟩ = ⟨c, by omega⟩ := Fin.ext rfl
    have h1 : (gᴴ * (Formalism.QuantumDeterminants.Hpk k r * g)) ⟨c, by omega⟩ q = Formalism.QuantumDeterminants.Hpk k r ⟨c, by omega⟩ q := by
      rw [← Matrix.mul_assoc, hU]
    rw [Matrix.mul_apply, Finset.sum_eq_single (⟨c, by omega⟩ : Fin (2 * r + k + 1))] at h1
    · have hd := hcol ⟨c, hcr⟩ ⟨c, by omega⟩ le_rfl
      rw [hE, if_pos rfl] at hd
      rw [Matrix.conjTranspose_apply, hd, star_one, one_mul] at h1
      exact h1
    · intro t _ htc
      rw [Matrix.conjTranspose_apply]
      have htc' : t.val ≠ c := fun h => htc (Fin.ext h)
      rcases Nat.lt_or_gt_of_ne htc' with hlt | hgt
      · have h2 := ih t.val hlt (by omega)
        simp only [Fin.eta] at h2
        rw [h2, Hpk_apply_of_lt_eq_ite k r t q (by omega), if_neg (by omega), mul_zero]
      · have hz := hcol ⟨c, hcr⟩ t (by simp; omega)
        rw [hE, if_neg htc] at hz
        rw [hz, star_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem nset_block_unitriangular : ∀ (k r : ℕ), ∀ g ∈ Nset k r, ∀ i j : Fin (2 * r + k + 1),
    lev k r j ≤ lev k r i → g i j = (1 : Mat k r) i j := by
  intro k r g hg i j hlev
  obtain ⟨hU, hcol, hmid⟩ := hg
  have hU' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hU
  rw [Matrix.one_apply]
  unfold GlobalTheory.CellDens.lev at hlev
  by_cases hj : j.val < r
  · have hij : j.val ≤ i.val := by split_ifs at hlev <;> omega
    have h := hcol ⟨j.val, hj⟩ i hij
    have he : Formalism.QuantumDeterminants.eI k r ⟨j.val, hj⟩ = j := Fin.ext rfl
    rw [he] at h
    exact h
  · by_cases hj2 : j.val ≤ r + k
    · have hi : r ≤ i.val := by split_ifs at hlev <;> omega
      exact hmid i j (by omega) hj2 hi
    · have hi : r + k < i.val ∧ j.val ≤ i.val := by split_ifs at hlev <;> omega
      have hC : 2 * r + k - i.val < r := by omega
      have h := Hpk_mul_apply_eq_Hpk_apply_of_lt_val k r g hU' hcol j (by omega) (2 * r + k - i.val) (by omega)
      rw [Matrix.mul_apply, Finset.sum_eq_single i] at h
      · rw [Hpk_apply_of_lt_eq_ite k r _ i hC, if_pos (by simp; omega), one_mul] at h
        rw [h, Hpk_apply_of_lt_eq_ite k r _ j hC]
        by_cases hij : i = j
        · subst hij
          rw [if_pos (by simp; omega), if_pos rfl]
        · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
          rw [if_neg (by simp; omega), if_neg hij]
      · intro s _ hs
        have hv : s.val ≠ i.val := fun h => hs (Fin.ext h)
        rw [Hpk_apply_of_lt_eq_ite k r _ s hC, if_neg (by simp; omega), zero_mul]
      · intro h'
        exact absurd (Finset.mem_univ _) h'

end GlobalTheory.CellDens
