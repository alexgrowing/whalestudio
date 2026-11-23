import Mathlib

namespace Bl.general_b_fact_third_bis_other

theorem goal1 :
  ∀ {R K V : Type} [inst : CommRing.{0} R] [IsDomain.{0} R] [inst_2 : Field.{0} K] [inst_3 : Algebra.{0, 0} R K]
  [IsFractionRing.{0, 0} R K] [inst_5 : AddCommGroup.{0} V] [inst_6 : Module.{0, 0} K V] [inst_7 : Module.{0, 0} R V]
  [IsScalarTower.{0, 0, 0} R K V] (N : Submodule.{0, 0} R V) {v : V},
  Membership.mem.{0, 0} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} N)) v →
    Exists.{1} fun (c : R) ↦ And (Ne.{1} c 0) (Membership.mem.{0, 0} N (HSMul.hSMul.{0, 0, 0} c v)) := by
  intro R K V _ _ _ _ _ _ _ _ _ N v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact N.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨d, hd, hdy⟩ := hy
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact N.smul_mem d hcx
    · rw [mul_smul]
      exact N.smul_mem c hdy
  | smul a x _ hx =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors R) a
    have hs : (s : R) ≠ 0 := nonZeroDivisors.ne_zero s.2
    refine ⟨c * s, mul_ne_zero hc hs, ?_⟩
    have key : (s : R) • (a • x) = r • x := by
      rw [← algebraMap_smul K (s : R) (a • x), smul_smul, mul_comm, hrs, algebraMap_smul]
    rw [mul_smul, key, smul_smul, mul_comm, ← smul_smul]
    exact N.smul_mem r hcx

end Bl.general_b_fact_third_bis_other
