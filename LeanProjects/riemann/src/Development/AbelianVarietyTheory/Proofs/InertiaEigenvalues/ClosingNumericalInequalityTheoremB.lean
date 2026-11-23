import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.UsedConclusionOfUsedInputs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory

theorem closing_numerical_inequality :
    ∀ (CA C b l S η Rw Tb Vd : ℝ) (f r t m p : ℕ), 13 * max CA 0 ≤ C → 260 * f ^ 2 * t ^ 2 * (r + t) ≤ p → 1 ≤ t → 1 ≤ f → m ≤ r → 3 ≤ l → 0 ≤ S → 0 ≤ η → 0 < b → 1 < Real.log b → Rw ≤ max CA 0 * (3 * (f : ℝ) * r * (4 * b / l + 2 * S + 2 * Real.logb l (2 * b) + 1 + η + t) + 6 * (f : ℝ) * m * (2 * b + 1)) + f → Tb ≤ 240 * (t : ℝ) ^ 2 * (f : ℝ) ^ 2 * ((r : ℝ) + t) * Real.log b → Vd ≤ 4 * ((r : ℝ) + t) * t → Rw + Tb + Vd ≤ C * f * (r * (b / l + S + t + η + Real.log b) + m * b) + (p : ℝ) * Real.log b := by
  intro CA C b l S η Rw Tb Vd f r t m p hC hp ht hf hm hl hS hη hb hL hRw hTb hVd
  have hK : 0 ≤ max CA 0 := le_max_right _ _
  have hpR : (260 : ℝ) * (f : ℝ) ^ 2 * (t : ℝ) ^ 2 * ((r : ℝ) + t) ≤ (p : ℝ) := by exact_mod_cast hp
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hmR : (m : ℝ) ≤ r := by exact_mod_cast hm
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hl0 : 0 < l := by linarith

  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hlogl : 1 ≤ Real.log l := by
    have := Real.log_le_log (by norm_num) hl
    linarith
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith

  have hlam : Real.logb l (2 * b) ≤ 2 * Real.log b := by
    rw [Real.logb, div_le_iff₀ (by linarith), Real.log_mul (by norm_num) hb.ne']
    nlinarith
  set L := Real.log b with hLdef
  set lam := Real.logb l (2 * b) with hlamdef
  have hx : 0 ≤ b / l := div_nonneg hb.le hl0.le
  set x := b / l with hxdef
  have h4x : 4 * b / l = 4 * x := by rw [hxdef]; ring
  rw [h4x] at hRw

  have hinner : 3 * (r : ℝ) * (4 * x + 2 * S + 2 * lam + 1 + η + t) + 6 * (m : ℝ) * (2 * b + 1)
      ≤ 13 * ((r : ℝ) * (x + S + t + η + L) + m * b) := by
    nlinarith [mul_nonneg hr0 hx, mul_nonneg hr0 hS, mul_nonneg hr0 (sub_nonneg.2 htR),
      mul_nonneg hr0 hη, mul_nonneg hr0 (sub_nonneg.2 hlam), mul_nonneg hr0 (by linarith : (0:ℝ) ≤ L),
      mul_nonneg hm0 hb.le]
  have hB : 0 ≤ (r : ℝ) * (x + S + t + η + L) + m * b := by
    have : 0 ≤ x + S + t + η + L := by linarith
    exact add_nonneg (mul_nonneg hr0 this) (mul_nonneg hm0 hb.le)
  have hf0 : (0 : ℝ) ≤ f := by linarith
  have hmain : max CA 0 * (3 * (f : ℝ) * r * (4 * x + 2 * S + 2 * lam + 1 + η + t) + 6 * (f : ℝ) * m * (2 * b + 1))
      ≤ C * f * ((r : ℝ) * (x + S + t + η + L) + m * b) := by
    have e : 3 * (f : ℝ) * r * (4 * x + 2 * S + 2 * lam + 1 + η + t) + 6 * (f : ℝ) * m * (2 * b + 1)
        = f * (3 * (r : ℝ) * (4 * x + 2 * S + 2 * lam + 1 + η + t) + 6 * (m : ℝ) * (2 * b + 1)) := by ring
    rw [e]
    calc max CA 0 * (f * (3 * (r : ℝ) * (4 * x + 2 * S + 2 * lam + 1 + η + t) + 6 * (m : ℝ) * (2 * b + 1)))
        ≤ max CA 0 * (f * (13 * ((r : ℝ) * (x + S + t + η + L) + m * b))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinner hf0) hK
      _ = (13 * max CA 0) * (f * ((r : ℝ) * (x + S + t + η + L) + m * b)) := by ring
      _ ≤ C * (f * ((r : ℝ) * (x + S + t + η + L) + m * b)) :=
          mul_le_mul_of_nonneg_right hC (mul_nonneg hf0 hB)
      _ = C * f * ((r : ℝ) * (x + S + t + η + L) + m * b) := by ring

  set Q : ℝ := (f : ℝ) ^ 2 * (t : ℝ) ^ 2 * ((r : ℝ) + t) with hQ
  have hQe : Q = (f : ℝ) ^ 2 * ((t : ℝ) ^ 2 * ((r : ℝ) + t)) := by rw [hQ]; ring
  have ht2 : (1 : ℝ) ≤ (t : ℝ) ^ 2 := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (t : ℝ) * t := mul_le_mul htR htR zero_le_one (by linarith)
      _ = (t : ℝ) ^ 2 := by ring
  have hf2 : (f : ℝ) ≤ (f : ℝ) ^ 2 := by
    calc (f : ℝ) = f * 1 := by ring
      _ ≤ (f : ℝ) * f := mul_le_mul_of_nonneg_left hfR hf0
      _ = (f : ℝ) ^ 2 := by ring
  have hrt : (1 : ℝ) ≤ (r : ℝ) + t := by linarith
  have hT1 : (1 : ℝ) ≤ (t : ℝ) ^ 2 * ((r : ℝ) + t) := one_le_mul_of_one_le_of_one_le ht2 hrt
  have hfQ : (f : ℝ) ≤ Q := by
    rw [hQe]
    exact hf2.trans (le_mul_of_one_le_right (sq_nonneg _) hT1)
  have hVQ : 4 * ((r : ℝ) + t) * t ≤ 4 * Q := by
    have h1 : ((r : ℝ) + t) * t ≤ (t : ℝ) ^ 2 * ((r : ℝ) + t) := by
      have : ((r : ℝ) + t) * t = ((r : ℝ) + t) * t * 1 := by ring
      calc ((r : ℝ) + t) * t ≤ ((r : ℝ) + t) * (t * t) :=
            mul_le_mul_of_nonneg_left (by
              calc (t : ℝ) = t * 1 := by ring
                _ ≤ (t : ℝ) * t := mul_le_mul_of_nonneg_left htR (by linarith)) (by linarith)
        _ = (t : ℝ) ^ 2 * ((r : ℝ) + t) := by ring
    have hf1 : (1 : ℝ) ≤ (f : ℝ) ^ 2 := hfR.trans hf2
    have h2 : (t : ℝ) ^ 2 * ((r : ℝ) + t) ≤ Q := by
      rw [hQe]; exact le_mul_of_one_le_left (by linarith) hf1
    linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hQL : Q ≤ Q * L := le_mul_of_one_le_right hQ0 hL.le
  have hTbQ : Tb ≤ 240 * Q * L := by
    have : 240 * (t : ℝ) ^ 2 * (f : ℝ) ^ 2 * ((r : ℝ) + t) * L = 240 * Q * L := by rw [hQ]; ring
    linarith
  have hpL : 260 * Q * L ≤ (p : ℝ) * L := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    have : 260 * Q = (260 : ℝ) * (f : ℝ) ^ 2 * (t : ℝ) ^ 2 * ((r : ℝ) + t) := by rw [hQ]; ring
    linarith
  have hQL0 : 0 ≤ Q * L := mul_nonneg hQ0 (by linarith)
  linarith

end GlobalTheory
