import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualOm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LogSubstExpSubOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpMvNegLogMvMul

noncomputable section

namespace GlobalTheory.ThBe0.Inhab

open MvPowerSeries Formalism.FG.InjVAux GlobalTheory.SubringSeries Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric GlobalTheory.ThBe0

variable {l : ℕ} [hl : Fact l.Prime] {κ : Type}

theorem pow_two_mul_inj {i j : ℕ} (h : l ^ (2 * i) = l ^ (2 * j)) : i = j := by
  have := Nat.pow_right_injective hl.out.two_le h
  omega

theorem coeff_logF_pow (j : ℕ) : PowerSeries.coeff (l ^ (2 * j)) (logF l) = ((l : ℂ_[l]) ^ j)⁻¹ := by
  rw [logF, PowerSeries.coeff_mk, Finset.sum_eq_single j, if_pos rfl]
  · intro i _ hi
    rw [if_neg fun h => hi (pow_two_mul_inj h).symm]
  · intro h
    exfalso
    apply h
    have := Nat.lt_pow_self (n := 2 * j) hl.out.one_lt
    simp only [Finset.mem_range]
    omega

theorem coeff_logF_cases (n : ℕ) : (PowerSeries.coeff n (logF l) = 0 ∧ ∀ j, n ≠ l ^ (2 * j)) ∨
    ∃ j, n = l ^ (2 * j) := by
  by_cases h : ∃ j, n = l ^ (2 * j)
  · exact Or.inr h
  · push Not at h
    refine Or.inl ⟨?_, h⟩
    rw [logF, PowerSeries.coeff_mk]
    exact Finset.sum_eq_zero fun j _ => if_neg (h j)

theorem coeff_one_logF : PowerSeries.coeff 1 (logF l) = 1 := by
  simpa using coeff_logF_pow (l := l) 0

theorem coeff_zero_logF : PowerSeries.coeff 0 (logF l) = 0 := by
  rcases coeff_logF_cases (l := l) 0 with h | ⟨j, h⟩
  · exact h.1
  · exact absurd h.symm (pow_ne_zero _ hl.out.ne_zero)

theorem cc_logF : PowerSeries.constantCoeff (logF l) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_logF]

def serM (l : ℕ) [Fact l.Prime] : MvPowerSeries (Fin 2) ℂ_[l] :=
  fun d => if d 0 ≤ d 1 then PowerSeries.coeff (d 0) (logF l) * PowerSeries.coeff (d 1) (logF l) else 0

theorem hasSubst_pair_padicComplex_of_constantCoeff_zero {x y : MvPowerSeries κ ℂ_[l]} (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    HasSubst (fun i : Fin 2 => if i = 0 then x else y) :=
  hasSubst_of_constantCoeff_zero fun i => by split_ifs <;> assumption

theorem subst_powerSeriesEvalTwoGroups {κ' : Type} {a : κ → MvPowerSeries κ' ℂ_[l]} (ha : HasSubst a)
    {x y : MvPowerSeries κ ℂ_[l]} (hx : constantCoeff x = 0) (hy : constantCoeff y = 0)
    (E : MvPowerSeries (Fin 2) ℂ_[l]) : subst a (at2 E x y) = at2 E (subst a x) (subst a y) := by
  rw [at2, at2, subst_comp_subst_apply (hasSubst_pair_padicComplex_of_constantCoeff_zero hx hy) ha]
  congr 1
  funext i
  split_ifs <;> rfl

theorem subst_psubst {κ' : Type} {a : κ → MvPowerSeries κ' ℂ_[l]} (ha : HasSubst a)
    {x : MvPowerSeries κ ℂ_[l]} (hx : constantCoeff x = 0) (f : PowerSeries ℂ_[l]) :
    subst a (f.subst x) = f.subst (subst a x) :=
  subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hx).const ha f

theorem isUnit_coeff_one : IsUnit (PowerSeries.coeff 1 (logF l)) := by
  rw [coeff_one_logF]; exact isUnit_one

def ex (u : MvPowerSeries κ ℂ_[l]) : MvPowerSeries κ ℂ_[l] :=
  ((logF l).substInvOfIsUnit isUnit_coeff_one).subst u

theorem cc_lg (k : κ) : constantCoeff (lg k : MvPowerSeries κ ℂ_[l]) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X k) _ cc_logF

def gAt (c : ℂ_[l]) (a b : MvPowerSeries κ ℂ_[l]) : MvPowerSeries κ ℂ_[l] :=
  C c * C (l : ℂ_[l])⁻¹ * (at2 (serM l) a (b ^ l) + at2 (serM l) b (a ^ l))

def beC (c : ℂ_[l]) : MvPowerSeries (Fin 2) ℂ_[l] := gAt c (ex (X 0)) (ex (X 1))

def Wf (l : ℕ) [Fact l.Prime] : Subring ℂ_[l] where
  carrier := {x | InWf x}
  mul_mem' := by
    rintro a b ⟨i, hi⟩ ⟨j, hj⟩
    exact ⟨i + j, by convert (Wp l).mul_mem hi hj using 1; ring⟩
  one_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨i, hi⟩ ⟨j, hj⟩
    refine ⟨i + j, ?_⟩
    convert (Wp l).add_mem ((Wp l).mul_mem ((Wp l).pow_mem (natCast_mem (Wp l) l) j) hi)
      ((Wp l).mul_mem ((Wp l).pow_mem (natCast_mem (Wp l) l) i) hj) using 1
    ring
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    rintro a ⟨i, hi⟩
    exact ⟨i, by simpa using hi⟩

section Frob

variable {σ : ℂ_[l] →+* ℂ_[l]}

abbrev Ph (σ : ℂ_[l] →+* ℂ_[l]) : MvPowerSeries κ ℂ_[l] →+* MvPowerSeries κ ℂ_[l] := frob l hl.out.ne_zero σ κ

end Frob

end GlobalTheory.ThBe0.Inhab
