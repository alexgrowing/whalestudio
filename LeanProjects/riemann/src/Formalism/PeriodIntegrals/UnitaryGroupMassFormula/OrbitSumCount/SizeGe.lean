import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitSumCount.TauPlBijective

noncomputable section

open scoped BigOperators
open Classical
open Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace SumOrbCW

variable {D : D7}

theorem size_ge {L : SizeData₂ D} {X : Inst D L} {E : Formalism.MainNotions.OrbitPlaces.Ent D} (hS : Formalism.MainNotions.OrbitPlaces.Shape D L X E)
    (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (z : Bool × HH D) :
    ((D.R.k : ℝ) - 1) * wPl D (i + 1) z ≤ E.size u i z := by
  by_cases ht : IsTopPl D z
  · have h1 := (hS.top u i hi z ht).1
    have h2 := hS.top1 u i hi z ht
    linarith
  · have h1 := (hS.low u i hi z ht).1
    linarith

theorem NN_le (i : ℕ) (hi : i < D.R.m) : (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) ≤ Nm D ^ 2 := by
  have h1 : D.R.N i ≤ D.R.N D.R.m := by
    unfold Formalism.BasicNotions.Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul hi.le le_rfl) _
  have h2 : D.R.N (i + 1) ≤ D.R.N D.R.m := by
    unfold Formalism.BasicNotions.Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul (Nat.succ_le_of_lt hi) le_rfl) _
  unfold Formalism.MainNotions.G.Nm
  rw [sq]
  exact mul_le_mul (by exact_mod_cast h1) (by exact_mod_cast h2) (by positivity) (by positivity)

theorem sumOrbC (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (E : Formalism.MainNotions.OrbitPlaces.Ent D) (C6 C : ℝ)
    (hS : Formalism.MainNotions.OrbitPlaces.Shape D L X E) (hC : Formalism.MainNotions.OrbitPlaces.CLarge C6 C K ce) : Formalism.MainNotions.OrbitPlaces.ValuationSumBound E L ce C := by
  intro p hp hp5 hc0 hh hpX u i hi
  have hp5' : (5 : ℝ) ≤ p := by exact_mod_cast hp5
  have hq : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hp1 : (1 : ℝ) < p := by linarith

  have ha1 := hS.xa
  have hpa : (p : ℝ) ≤ L.sc.a := le_trans hpX ha1.1
  have hLg : 1 ≤ Real.logb p L.sc.a := by
    rw [Real.le_logb_iff_rpow_le hp1 (by linarith), Real.rpow_one]; exact hpa
  have hlog2 : Real.logb p (L.sc.a ^ 2) = 2 * Real.logb p L.sc.a := by
    unfold Real.logb; rw [Real.log_pow]; push_cast; ring

  set S := ∑ τ : D.what₂.Tau, wj D (i + 1) τ with hSdef
  have hFI : FInert D (i + 1) p = ((D.R.k : ℝ) - 1) * S / ((p : ℝ) ^ 2 - 1) := by
    unfold FInert; rw [if_pos ⟨hc0, hh⟩, hSdef, Finset.mul_sum, Finset.sum_div]
  have hS0 : 0 ≤ S := by
    rw [hSdef, ← sum_wPl D (i + 1)]
    exact Finset.sum_nonneg fun z _ => (hS.wpos i hi z).le
  have hsz : ((D.R.k : ℝ) - 1) * S ≤ ∑ z : Bool × HH D, E.size u i z := by
    rw [hSdef, ← sum_wPl D (i + 1), Finset.mul_sum]
    exact Finset.sum_le_sum fun z _ => size_ge hS u i hi z

  have hCL : C * (2 * Real.logb p L.sc.a + 1) ≤ ce.dig * Real.logb p L.sc.a := by
    have e1 : C * (2 * Real.logb p L.sc.a + 1) ≤ 3 * C * Real.logb p L.sc.a := by
      nlinarith [mul_nonneg hC.nonneg (sub_nonneg.2 hLg)]
    have e2 : 3 * C * Real.logb p L.sc.a ≤ ce.dig * Real.logb p L.sc.a :=
      mul_le_mul_of_nonneg_right hC.dig (by linarith)
    linarith
  have hNN := NN_le (D := D) i hi
  have hf : (0 : ℝ) ≤ D.R.f := by positivity
  have hB : (D.R.f : ℝ) * D.R.N i * D.R.N (i + 1) * (C * (2 * Real.logb p L.sc.a + 1)) ≤
      ((D.R.f : ℝ) * Nm D ^ 2) * (ce.dig * Real.logb p L.sc.a) := by
    rw [mul_assoc (D.R.f : ℝ)]
    refine mul_le_mul (mul_le_mul_of_nonneg_left hNN hf) hCL
      (by nlinarith [hC.nonneg, hLg]) (by positivity)
  unfold EatC Formalism.MainNotions.product_zeroth_first_parts.rho
  rw [hFI, hlog2]
  have hdiv : ((D.R.k : ℝ) - 1) * S / ((p : ℝ) ^ 2 - 1) ≤ 1 / ((p : ℝ) ^ 2 - 1) * ∑ z : Bool × HH D, E.size u i z := by
    rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right hsz hq.le
  have hS1 : 0 ≤ S / ((p : ℝ) ^ 2 - 1) := div_nonneg hS0 hq.le
  nlinarith [hdiv, hS1, hB]

end SumOrbCW

end
