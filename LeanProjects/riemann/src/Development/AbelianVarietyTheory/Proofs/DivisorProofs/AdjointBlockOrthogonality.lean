import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult.AdPCasimir

variable {R S : ℕ}

lemma adP_Eab_eq (a b : Ix R S) (y z : NC R S) :
    adP (Eab b a) y z = (if y.1 = (b, z.1.2) then (if a = z.1.1 then 1 else 0) else 0)
      - (if y.1 = (z.1.1, a) then (if b = z.1.2 then 1 else 0) else 0) := by
  obtain ⟨⟨y1, y2⟩, hy⟩ := y
  obtain ⟨⟨z1, z2⟩, hz⟩ := z
  simp only [adP, Formalism.BasicNotions.TH.Eab, Matrix.single_apply, Prod.mk.injEq]
  congr 1
  · by_cases h1 : y1 = b <;> by_cases h2 : y2 = z2 <;> by_cases h3 : a = z1 <;> simp [h1, h2, h3, eq_comm]
    exact fun h => h1 h.symm
  · by_cases h1 : y1 = z1 <;> by_cases h2 : y2 = a <;> by_cases h3 : b = z2 <;> simp [h1, h2, h3, eq_comm]
    exact fun h => h2 h.symm

lemma sum_point (p q : Ix R S × Ix R S) (c d : ℂ) :
    ∑ y : NC R S, (if y.1 = p then c else 0) * (if y.1 = q then d else 0)
      = if ¬ sameBlock p.1 p.2 ∧ p = q then c * d else 0 := by
  by_cases hp : sameBlock p.1 p.2
  · rw [if_neg (by simp [hp])]
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [if_neg, zero_mul]
    rintro rfl
    exact y.2 hp
  · rw [Finset.sum_eq_single (⟨p, hp⟩ : NC R S)]
    · by_cases h : p = q <;> simp [h, hp]
      subst h
      simp [hp]
    · intro y _ hy
      rw [if_neg, zero_mul]
      intro h
      exact hy (Subtype.ext h)
    · simp

lemma star_adP (a b : Ix R S) (y z : NC R S) :
    (starRingEnd ℂ) (adP (Eab b a) y z) = adP (Eab b a) y z := by
  rw [adP_Eab_eq]
  split_ifs <;> simp

theorem sum_adP_mul_adP (R S : ℕ) (z w : NC R S) :
    ∑ a : Ix R S, ∑ b : Ix R S, (if sameBlock a b then
      ∑ y : NC R S, (starRingEnd ℂ) (adP (Eab b a) y z) * adP (Eab b a) y w else 0)
      = if z = w then ((R + S : ℕ) : ℂ) else 0 := by
  simp only [star_adP]
  simp only [adP_Eab_eq, sub_mul, mul_sub, Finset.sum_sub_distrib, sum_point]
  obtain ⟨⟨z1, z2⟩, hz⟩ := z
  obtain ⟨⟨w1, w2⟩, hw⟩ := w
  simp only [Subtype.mk.injEq, Prod.mk.injEq]
  rcases z1 with z1 | z1 <;> rcases z2 with z2 | z2 <;> rcases w1 with w1 | w1 <;> rcases w2 with w2 | w2 <;>
    first
    | exact absurd trivial hz
    | exact absurd trivial hw
    | skip
  all_goals
    simp [Fintype.sum_sum_type, Formalism.BasicNotions.TH.sameBlock, Finset.sum_add_distrib]
  all_goals
    by_cases h1 : z1 = w1 <;> by_cases h2 : z2 = w2 <;> simp [h1, h2, eq_comm, add_comm]

end GlobalTheory.SteepMult.AdPCasimir
