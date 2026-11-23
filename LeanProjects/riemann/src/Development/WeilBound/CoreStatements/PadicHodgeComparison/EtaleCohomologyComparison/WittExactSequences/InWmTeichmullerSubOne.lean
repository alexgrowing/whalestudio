import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.DesAcrZero
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ForD

set_option backward.isDefEq.respectTransparency false

open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.D

variable (l : ℕ) [Fact l.Prime]

theorem out : Out l := out_of_rin l (CrystallineSemistableComparison.R.forD l)

theorem not_isUnit_pFlat : ¬ IsUnit (pFlat l) := fun h => by
  have := h.map (PreTilt.untilt (O := OC l) (p := l))
  rw [untilt_pFlat] at this
  exact (Fact.out : ¬ IsUnit (l : OC l)) this

theorem inWm_rtW (k : ℕ) : InWm l (rtW l k) := by
  intro i hi
  cases i with
  | zero =>
    rw [rtW, WittVector.teichmuller_coeff_zero] at hi
    have := hi.map (iterateFrobeniusEquiv (Ob l) l k)
    rw [rt, RingEquiv.apply_symm_apply] at this
    exact not_isUnit_pFlat l this
  | succ i =>
    rw [rtW, WittVector.teichmuller_coeff_pos l _ _ (Nat.succ_pos i)] at hi
    exact not_isUnit_pFlat l (isUnit_of_dvd_unit (dvd_zero _) hi)

theorem inWm_iff [IsLocalRing (Ob l)] (s : Ainf l) : InWm l s ↔ WittVector.map (IsLocalRing.residue (Ob l)) s = 0 := by
  rw [WittVector.ext_iff]
  refine forall_congr' fun i => ?_
  rw [WittVector.map_coeff, WittVector.zero_coeff, IsLocalRing.residue_eq_zero_iff]
  rfl

theorem isLocalRing_Ob (h : ObFacts l) : IsLocalRing (Ob l) := by
  obtain ⟨_, _, _⟩ := h
  infer_instance

theorem inWm_teichmuller_sub_one (h : ObFacts l) (x : Ob l) (hx : ¬ IsUnit (x - 1)) :
    InWm l (WittVector.teichmuller l x - 1) := by
  have := isLocalRing_Ob l h
  have e : IsLocalRing.residue (Ob l) x = 1 := by
    rw [← sub_eq_zero, ← map_one (IsLocalRing.residue (Ob l)), ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hx
  rw [inWm_iff, map_sub, WittVector.map_teichmuller, e, map_one, map_one, sub_self]

theorem InWm.mul_left (h : ObFacts l) (a : Ainf l) {s : Ainf l} (hs : InWm l s) : InWm l (a * s) := by
  have := isLocalRing_Ob l h
  rw [inWm_iff] at hs ⊢
  rw [map_mul, hs, mul_zero]

end CrystallineSemistableComparison.D
