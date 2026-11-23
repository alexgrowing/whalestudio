import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerSide
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerExtra
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerRest
import GroundTheory.HeightsAndTheta.Heights.Intersections.CardLength
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KrullDimQuotientEqOneIffEqBot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem geoNum_zero_nonneg {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (b : Fin 0 → K → ℤ) : 0 ≤ geoNum 0 W b := by
  unfold geoNum
  split_ifs <;> positivity

theorem span_singleton_eq_range_lsmul {A : Type*} [CommRing A] (x : A) :
    Ideal.span {x} = LinearMap.range (LinearMap.lsmul A A x) := by
  ext z
  simp [Ideal.mem_span_singleton', LinearMap.mem_range, mul_comm]

theorem regularityLocalCardinality_holds.proof (hD : regularityLocalDimension_holds.Statement) (hR : regularityLocalResidue_holds.Statement) : regularityLocalCardinality_holds.Statement := by
  intro K _ ι _ P s a W b y hP hs hsP hW hy hy0
  obtain ⟨hloc, hnoeth, hdim⟩ := hD K ι P s a W hP hs hsP hW
  have := hloc
  have := hnoeth
  have : P.IsPrime := hP.2.1.1
  have : IsDomain (locRing P W) := inferInstance
  have : Ring.KrullDimLE 1 (locRing P W) := ReciprocityTheory.ChartRestriction.G.AI.krullDimLE_one_of_krullDim_eq hdim
  obtain ⟨-, hcard⟩ := hR K ι P s a W b hP hs hsP hW
  have hy0' : (⟨y, hy⟩ : locRing P W) ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  have hfin : Module.length (locRing P W) (locRing P W ⧸ locIdeal P W y) ≠ ⊤ := by
    rw [locIdeal_eq_span hy, span_singleton_eq_range_lsmul]
    exact ReciprocityTheory.ChartRestriction.G.AI.length_coker_ne_top (locRing P W) hy0'
  rw [card_eq_card_residueField_pow_length _ hfin, hcard]
  have hg : (geoNum 0 W b : ℝ) = ((geoNum 0 W b).toNat : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg (geoNum_zero_nonneg W b)).symm
  rw [hg]
  push_cast
  rw [Real.log_pow, Real.log_pow]

end

end GroundTheory.Heights₂.Heights.Inter
