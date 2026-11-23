import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsLocalCoeffLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem localizedModule_quot_nontrivial {R : Type u} [CommRing R] (J W : Ideal R) [W.IsPrime]
    (hJW : J ≤ W) : Nontrivial (LocalizedModule W.primeCompl (R ⧸ J)) := by
  refine ⟨⟨LocalizedModule.mk (1 : R ⧸ J) 1, 0, fun h => ?_⟩⟩
  rw [← LocalizedModule.zero_mk (1 : W.primeCompl), LocalizedModule.mk_eq] at h
  obtain ⟨v, hv⟩ := h
  have hv' : ((v : R) : R ⧸ J) = 0 := by
    simpa [Submonoid.smul_def, Algebra.smul_def] using hv
  exact v.2 (hJW (Ideal.Quotient.eq_zero_iff_mem.mp hv'))

theorem LocCyclePos.proof : LocCyclePos.Statement := by
  intro R _ _ J W hW
  have : W.IsPrime := hW.1.1
  have hfin := ReciprocityTheory.ChartRestriction.G.AI.I1.locLen_ne_top hW
  unfold ReciprocityTheory.ChartRestriction.G.AI.locLen at hfin
  have := localizedModule_quot_nontrivial J W hW.1.2
  have hpos : 0 < Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) :=
    Module.length_pos
  unfold locCycle
  rw [dif_pos hW]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  simp only at hn
  rw [← hn] at hpos ⊢
  simp only [ENat.toNat_natCast, Nat.cast_pos]
  exact_mod_cast hpos

end

end GroundTheory.Heights₂.Heights.NumbersDVR
