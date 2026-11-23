import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
open Matrix Complex
namespace GlobalTheory.SW

private theorem intM_add_iff_of_intM_right {K : Type} [Field K] {κ ι : Type} {x y : Matrix κ ι K} (hy : IntM y) :
    IntM (x + y) ↔ IntM x :=
  ⟨fun h k i => by simpa using (h k i).sub (hy k i), fun h k i => (h k i).add (hy k i)⟩

open Classical in

theorem ind_sb {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι] :
    HasLevel 1 (fun x : Matrix κ ι K => if IntM x then (1:ℂ) else 0) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · rw [Nat.cast_one, one_smul]
    by_contra h
    exact hx (if_neg h)
  · rw [Nat.cast_one, one_smul]
    exact if_congr (intM_add_iff_of_intM_right hy) rfl rfl

open Classical in

theorem ind_isSB {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι] :
    IsSB (fun x : Matrix κ ι K => if IntM x then (1:ℂ) else 0) := ⟨1, one_pos, ind_sb⟩

open Classical in

theorem ind_ne_zero {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι] :
    (fun x : Matrix κ ι K => if IntM x then (1:ℂ) else 0) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [if_pos (show IntM (0 : Matrix κ ι K) from fun k i => by simpa using isIntegral_zero)] at h0
  exact one_ne_zero h0

end GlobalTheory.SW
