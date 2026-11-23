import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TotallyDisjointProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead

namespace GlobalTheory.TotDisjUnlinked

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem absPow_val_eq_zpow (s : ℂ) (x : kˣ) :
    (absPow k s x : ℂ) = ((resCard k : ℂ) ^ (-s)) ^ (SmGL.ord k x : ℤ) := by
  have hq : (0 : ℝ) < resCard k := by exact_mod_cast zero_lt_one.trans (SplitWeil.one_lt_resCard k)
  have hq' : (resCard k : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [val_absPow, LGrp.nabs_eq_zpow, Complex.cpow_def_of_ne_zero (by exact_mod_cast (zpow_pos hq _).ne'),
    Complex.cpow_def_of_ne_zero hq', ← Complex.ofReal_log (zpow_pos hq _).le, Real.log_zpow,
    ← Complex.exp_int_mul, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

theorem absPow_eq_unrChar (s : ℂ) :
    absPow k s = unrChar k (Units.mk0 ((resCard k : ℂ) ^ (-s))
      (by
        have hq : (0 : ℝ) < resCard k := by exact_mod_cast zero_lt_one.trans (SplitWeil.one_lt_resCard k)
        exact Complex.cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast hq.ne')))) := by
  ext x
  rw [absPow_val_eq_zpow, unrChar_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0]

end GlobalTheory.TotDisjUnlinked

theorem GlobalTheory.TotDisjUnlinked.main :
    GlobalTheory.Published.TotallyDisjointProductIrreducible → GlobalTheory.Published.UnlinkedProductIrreducible := by
  intro H k _ _ _ _ r t s s' π₁ π₂ d d' σ σ' h₁ h₂ hu
  refine H k r t s s' π₁ π₂ d d' σ σ' h₁ h₂ fun a b h j _ => ?_
  rw [GlobalTheory.TotDisjUnlinked.absPow_eq_unrChar]
  exact hu a b h _
