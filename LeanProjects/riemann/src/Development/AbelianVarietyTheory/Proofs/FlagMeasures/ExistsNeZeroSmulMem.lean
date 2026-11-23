import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed

open NumberField

namespace GlobalTheory.NonzeroIntegerSmulMem

theorem exists_ne_zero_smul_mem {E : Type} [Field E] [NumberField E] [StarRing E]
    {S : Formalism.BasicNotions.HSpace E} (L : Submodule (RingOfIntegers E) (Formalism.BasicNotions.HSpace.V S))
    (hL : Submodule.IsLattice E L) (x : Formalism.BasicNotions.HSpace.V S) :
    ∃ r : RingOfIntegers E, r ≠ (0 : RingOfIntegers E) ∧ r • x ∈ L := by

  have hx : x ∈ Submodule.span E (L : Set (Formalism.BasicNotions.HSpace.V S)) := by
    rw [hL.span_eq_top]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨r, hr, hrL⟩ := hy
    obtain ⟨t, ht, htL⟩ := hz
    refine ⟨r * t, mul_ne_zero hr ht, ?_⟩
    have e : (r * t) • (y + z) = t • (r • y) + r • (t • z) := by
      rw [smul_add, mul_smul, mul_smul, smul_comm r t y]
    rw [e]
    exact L.add_mem (L.smul_mem t hrL) (L.smul_mem r htL)
  | smul a y _ hy =>
    obtain ⟨r, hr, hrL⟩ := hy

    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers E)) a
    refine ⟨r * (d : RingOfIntegers E), mul_ne_zero hr (nonZeroDivisors.coe_ne_zero d), ?_⟩
    have e1 : (d : RingOfIntegers E) • a = algebraMap (RingOfIntegers E) E n := by
      rw [Algebra.smul_def, mul_comm]
      exact hnd
    have e : (r * (d : RingOfIntegers E)) • (a • y) = n • (r • y) := by
      rw [mul_smul, ← smul_assoc (d : RingOfIntegers E) a y, e1, algebraMap_smul E n y,
        smul_comm r n y]
    rw [e]
    exact L.smul_mem n hrL

end GlobalTheory.NonzeroIntegerSmulMem
