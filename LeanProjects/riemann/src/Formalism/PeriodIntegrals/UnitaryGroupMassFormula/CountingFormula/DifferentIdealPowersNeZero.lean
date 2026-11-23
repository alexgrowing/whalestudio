import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DifferentIdealPowers

open NumberField Module Formalism.MainNotions.S

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

def SStable {K : Type} [Field K] [NumberField K] [StarRing K]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Prop :=
  ∀ a ∈ (I : Submodule (𝓞 K) K), star a ∈ (I : Submodule (𝓞 K) K)

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem sStable_one : SStable (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
  intro a ha
  rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff] at ha ⊢
  obtain ⟨x, rfl⟩ := ha
  exact ⟨NumberField.RingOfIntegers.mapRingHom (starRingEnd K) x, rfl⟩

theorem sStable_mul {I J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : SStable I) (hJ : SStable J) :
    SStable (I * J) := by
  intro a ha
  rw [FractionalIdeal.coe_mul] at ha ⊢
  refine Submodule.mul_induction_on (C := fun a => star a ∈ (I : Submodule (𝓞 K) K) * J) ha ?_ ?_
  · intro x hx y hy
    rw [star_mul, mul_comm (star y)]
    exact Submodule.mul_mem_mul (hI x hx) (hJ y hy)
  · intro x y hx hy
    rw [star_add]
    exact add_mem hx hy

theorem sStable_pow {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : SStable I) (n : ℕ) :
    SStable (I ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact sStable_one
  | succ n ih => rw [pow_succ]; exact sStable_mul ih hI

theorem sStable_inv {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : SStable I) : SStable I⁻¹ := by
  by_cases h0 : I = 0
  · subst h0
    intro a ha
    rw [FractionalIdeal.inv_zero', FractionalIdeal.coe_zero, Submodule.mem_bot] at ha ⊢
    rw [ha, star_zero]
  · intro a ha
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_inv_iff h0] at ha ⊢
    intro y hy
    have h1 : a * star y ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
      ha _ (FractionalIdeal.mem_coe.mp (hI y (FractionalIdeal.mem_coe.mpr hy)))
    have h2 := sStable_one (K := K) _ (FractionalIdeal.mem_coe.mpr h1)
    rw [star_mul, star_star, mul_comm] at h2
    exact FractionalIdeal.mem_coe.mp h2

theorem sStable_zpow {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : SStable I) (n : ℤ) :
    SStable (I ^ n) := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_coe, zpow_natCast]; exact sStable_pow hI n
  | negSucc n => rw [zpow_negSucc]; exact sStable_inv (sStable_pow hI _)

end Generic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sStable_ddS (D : Formalism.BasicNotions.D7) : SStable (ddS D) := by
  intro a ha
  rw [FractionalIdeal.mem_coe] at ha ⊢
  unfold ddS at ha ⊢
  rw [FractionalIdeal.mem_coeIdeal] at ha ⊢
  obtain ⟨y, hy, rfl⟩ := ha

  have hc : (NumberField.RingOfIntegers.mapRingHom (starRingEnd D.host.E)).comp
      (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) := by
    ext x
    exact (D.sp.cm.fixed _).2 ⟨(x : D.host.F), rfl⟩
  refine ⟨NumberField.RingOfIntegers.mapRingHom (starRingEnd D.host.E) y, ?_, rfl⟩
  rw [← hc, ← Ideal.map_map]
  exact Ideal.mem_map_of_mem _ hy

theorem ddS_ne_zero' (D : Formalism.BasicNotions.D7) : ddS D ≠ 0 := by
  unfold ddS
  rw [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
  exact Ideal.map_ne_bot_of_ne_bot (differentIdeal_ne_bot)

theorem stable_differentIdealPowers (D : Formalism.BasicNotions.D7) (i : Fin (D.R.rS + 1)) : SStable (differentIdealPowers D i) := by
  induction i using Fin.lastCases with
  | last => unfold differentIdealPowers; rw [Fin.snoc_last]; exact sStable_one
  | cast a => unfold differentIdealPowers; rw [Fin.snoc_castSucc]; exact sStable_zpow (sStable_ddS D) _

theorem differentIdealPowers_ne_zero (D : Formalism.BasicNotions.D7) (i : Fin (D.R.rS + 1)) : differentIdealPowers D i ≠ 0 := by
  induction i using Fin.lastCases with
  | last => unfold differentIdealPowers; rw [Fin.snoc_last]; exact one_ne_zero
  | cast a => unfold differentIdealPowers; rw [Fin.snoc_castSucc]; exact zpow_ne_zero _ (ddS_ne_zero' D)

end PI.UnitaryGroupMassFormula.CntFormula.R6
