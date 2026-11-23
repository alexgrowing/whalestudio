import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity

open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity Classical

noncomputable section
namespace GlobalTheory.HerbrandBridge

variable {C : Type} [Field C]

def toAddVal (w : Valuation C ℝ≥0) (ℓ : C) (h0 : 0 < w ℓ) (h1 : w ℓ < 1) :
    AddValuation C (WithTop ℝ) :=
  AddValuation.of
    (fun x => if x = 0 then ⊤ else ((Real.log (w x : ℝ) / Real.log (w ℓ : ℝ) : ℝ) : WithTop ℝ))
    (by simp) (by simp)
    (by
      have hL : Real.log (w ℓ : ℝ) < 0 :=
        Real.log_neg (by exact_mod_cast h0) (by exact_mod_cast h1)
      have key : ∀ x z : C, z ≠ 0 → w z ≤ w x →
          Real.log (w x : ℝ) / Real.log (w ℓ : ℝ) ≤ Real.log (w z : ℝ) / Real.log (w ℓ : ℝ) := by
        intro x z hz hle
        apply div_le_div_of_nonpos_of_le hL.le
        apply Real.log_le_log
        · have := (Valuation.ne_zero_iff w).2 hz
          exact_mod_cast pos_iff_ne_zero.2 this
        · exact_mod_cast hle
      intro x y
      by_cases hxy : x + y = 0
      · simp [hxy]
      by_cases hx : x = 0
      · subst hx; simp
      by_cases hy : y = 0
      · subst hy; simp
      simp only [hx, hy, hxy, if_false]
      rcases le_max_iff.1 (w.map_add x y) with h | h
      · exact min_le_of_left_le (WithTop.coe_le_coe.2 (key x _ hxy h))
      · exact min_le_of_right_le (WithTop.coe_le_coe.2 (key y _ hxy h)))
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx; simp
      by_cases hy : y = 0
      · subst hy; simp
      have hx' : (0 : ℝ) < w x := by
        have := (Valuation.ne_zero_iff w).2 hx; exact_mod_cast pos_iff_ne_zero.2 this
      have hy' : (0 : ℝ) < w y := by
        have := (Valuation.ne_zero_iff w).2 hy; exact_mod_cast pos_iff_ne_zero.2 this
      simp only [mul_eq_zero, hx, hy, or_self, if_false, map_mul, NNReal.coe_mul]
      rw [Real.log_mul hx'.ne' hy'.ne', add_div]
      rfl)

theorem toAddVal_apply (w : Valuation C ℝ≥0) (ℓ : C) (h0 : 0 < w ℓ) (h1 : w ℓ < 1) (x : C) :
    toAddVal w ℓ h0 h1 x =
      if x = 0 then ⊤ else ((Real.log (w x : ℝ) / Real.log (w ℓ : ℝ) : ℝ) : WithTop ℝ) := rfl

theorem mem_addValuationIntegerRing_normalized_iff (w : Valuation C ℝ≥0) (ℓ : C) (h0 : 0 < w ℓ) (h1 : w ℓ < 1) (x : C) :
    x ∈ Int0 (toAddVal w ℓ h0 h1) ↔ x ∈ w.valuationSubring := by
  rw [mem_addValuationIntegerRing_iff, toAddVal_apply, Valuation.mem_valuationSubring_iff]
  by_cases hx : x = 0
  · simp [hx]
  have hL : Real.log (w ℓ : ℝ) < 0 :=
    Real.log_neg (by exact_mod_cast h0) (by exact_mod_cast h1)
  have hx' : (0 : ℝ) < w x := by
    have := (Valuation.ne_zero_iff w).2 hx; exact_mod_cast pos_iff_ne_zero.2 this
  simp only [hx, if_false]
  rw [← WithTop.coe_zero, WithTop.coe_le_coe, div_nonneg_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact absurd h (not_le.2 hL)
    · have := (Real.log_nonpos_iff hx'.le).1 h
      exact_mod_cast this
  · intro h
    right
    exact ⟨Real.log_nonpos hx'.le (by exact_mod_cast h), hL.le⟩

theorem toAddVal_of_ne (w : Valuation C ℝ≥0) (ℓ : C) (h0 : 0 < w ℓ) (h1 : w ℓ < 1) {x : C}
    (hx : x ≠ 0) : toAddVal w ℓ h0 h1 x = ((GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.addVal w ℓ x : ℝ) : WithTop ℝ) := by
  rw [toAddVal_apply, if_neg hx]; rfl

variable {S : Type} [Fintype S] [DecidableEq S]

def liftA {w : Valuation C ℝ≥0} {v : AddValuation C (WithTop ℝ)}
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (a : S → w.valuationSubring) : S → Int0 v :=
  fun s => ⟨a s, (hv _).2 (a s).2⟩

def evalVec {v : AddValuation C (WithTop ℝ)} (a : S → Int0 v) (N : ℕ) (x : Fin N → RS a) :
    S → Fin N → C :=
  fun s i => ((ev a s (x i) : Int0 v) : C)

def filPre {w : Valuation C ℝ≥0} {v : AddValuation C (WithTop ℝ)} (a : S → Int0 v) {N : ℕ}
    (F : Submodule w.valuationSubring (S → Fin N → C)) : Submodule (RS a) (Fin N → RS a) :=
  Submodule.span (RS a) {x | evalVec a N x ∈ F}

end GlobalTheory.HerbrandBridge

namespace GlobalTheory.HerbrandBridge
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference (freeLattice unif IsFiltration filSpace eigenSub eigenQuot lie quotMap addVal
  DetRel IsLatticeBasis HasVal)

variable {C : Type} [Field C] {S : Type} [Fintype S] [DecidableEq S]

theorem evalVec_smul {v : AddValuation C (WithTop ℝ)} (a : S → Int0 v) (N : ℕ) (c : Int0 v)
    (x : Fin N → RS a) : evalVec a N (c • x) = fun s i => (c : C) * evalVec a N x s i := by
  funext s i
  simp only [evalVec, Pi.smul_apply, map_smul, smul_eq_mul, Subring.coe_mul]

theorem evalVec_add {v : AddValuation C (WithTop ℝ)} (a : S → Int0 v) (N : ℕ)
    (x y : Fin N → RS a) : evalVec a N (x + y) = evalVec a N x + evalVec a N y := by
  funext s i
  simp only [evalVec, Pi.add_apply, map_add, Subring.coe_add]

theorem evalVec_sub {v : AddValuation C (WithTop ℝ)} (a : S → Int0 v) (N : ℕ)
    (x y : Fin N → RS a) : evalVec a N (x - y) = evalVec a N x - evalVec a N y := by
  funext s i
  simp only [evalVec, Pi.sub_apply, map_sub]; rfl

theorem comp_coe {v : AddValuation C (WithTop ℝ)} (a : S → Int0 v) (N : ℕ) (s : S)
    (x : Fin N → RS a) : (fun i => ((comp a N s x i : Int0 v) : C)) = evalVec a N x s := rfl

end GlobalTheory.HerbrandBridge
