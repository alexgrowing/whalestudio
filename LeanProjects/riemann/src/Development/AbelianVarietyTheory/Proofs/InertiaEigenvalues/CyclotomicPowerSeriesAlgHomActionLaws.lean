import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CyclotomicFrobeniusPowerSeriesXEqMulQuotient

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

namespace GlobalTheory.Cyc

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

theorem cyc_eq_binomialSeries (c : ℤ_[l]) : cyc l O c = PowerSeries.binomialSeries O c - 1 := by
  rw [cyc, GlobalTheory.Fon.map_binomialSeries _ (fun _ => rfl)]

theorem act_X (c : ℤ_[l]) : act l O c PowerSeries.X = cyc l O c := PowerSeries.substAlgHom_X _

theorem act_apply (c : ℤ_[l]) (a : PowerSeries O) :
    act l O c a = PowerSeries.subst (cyc l O c) a :=
  congrFun (PowerSeries.coe_substAlgHom _) a

theorem act_eq_gam (c : ℤ_[l]) : act l O c = GlobalTheory.Fon.gam O c :=
  GlobalTheory.Fon.algHom_ext_X (by rw [act_X, GlobalTheory.Fon.gam_X, cyc_eq_binomialSeries])
    (by rw [act_X, cyc_const])

theorem act_act (c c' : ℤ_[l]) (a : PowerSeries O) :
    act l O c (act l O c' a) = act l O (c * c') a := by
  simp only [act_eq_gam, GlobalTheory.Fon.gam_mul]

theorem act_one (a : PowerSeries O) : act l O 1 a = a := by
  rw [act_eq_gam, GlobalTheory.Fon.gam_one]

theorem cyc_natCast (k : ℕ) : cyc l O (k : ℤ_[l]) = (1 + PowerSeries.X) ^ k - 1 := by
  rw [cyc_eq_binomialSeries, PowerSeries.binomialSeries_nat]

theorem coeff_one_cyc (c : ℤ_[l]) : PowerSeries.coeff 1 (cyc l O c) = algebraMap ℤ_[l] O c := by
  rw [cyc_eq_binomialSeries, ← GlobalTheory.Fon.gam_X, GlobalTheory.Fon.coeff_one_gam_X]

theorem act_pow_sub_one (c : ℤ_[l]) (k : ℕ) :
    act l O c ((1 + PowerSeries.X) ^ k - 1) =
      PowerSeries.subst ((1 + PowerSeries.X) ^ k - 1 : PowerSeries O) (cyc l O c) := by
  rw [← cyc_natCast l O k, ← act_apply, ← act_X l O c, ← act_X l O (k : ℤ_[l]), act_act, act_act,
    mul_comm]

theorem act_laws : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], (∀ c, act l O c PowerSeries.X = cyc l O c) ∧ (∀ c c' a, act l O c (act l O c' a) = act l O (c * c') a) ∧ (∀ a, act l O 1 a = a) ∧ (∀ k : ℕ, cyc l O (k : ℤ_[l]) = (1 + PowerSeries.X) ^ k - 1) ∧ (∀ c, PowerSeries.coeff 1 (cyc l O c) = algebraMap ℤ_[l] O c) ∧ ∀ (c : ℤ_[l]) (k : ℕ), act l O c ((1 + PowerSeries.X) ^ k - 1) = PowerSeries.subst ((1 + PowerSeries.X) ^ k - 1 : PowerSeries O) (cyc l O c) :=
  fun l _ O _ _ => ⟨act_X l O, act_act l O, act_one l O, cyc_natCast l O, coeff_one_cyc l O,
    act_pow_sub_one l O⟩

end GlobalTheory.Cyc
