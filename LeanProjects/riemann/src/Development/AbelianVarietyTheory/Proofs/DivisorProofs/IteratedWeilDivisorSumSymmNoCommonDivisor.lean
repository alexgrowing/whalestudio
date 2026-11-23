import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumMultResCycIndicatorSymmStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixHt

theorem finsum_mul_comp_eq_sum_indicator {W Z : Type*} (c : W → ℝ) (hc : (Function.support c).Finite) (f : W → Z)
    (F : Finset Z) (hF : f '' Function.support c ⊆ ↑F) (g : Z → ℝ) :
    ∑ᶠ w, c w * g (f w) = ∑ x ∈ F, g x * ∑ᶠ w, c w * Set.indicator {x} 1 (f w) := by
  classical
  have hsub : ∀ h : Z → ℝ, Function.support (fun w => c w * h (f w)) ⊆ ↑hc.toFinset := fun h w hw => by
    rw [Set.Finite.coe_toFinset]; exact left_ne_zero_of_mul hw
  rw [finsum_eq_sum_of_support_subset _ (hsub g)]
  have e : ∀ x : Z, ∑ᶠ w, c w * Set.indicator {x} 1 (f w) = ∑ w ∈ hc.toFinset, c w * Set.indicator {x} 1 (f w) :=
    fun x => finsum_eq_sum_of_support_subset _ (hsub (Set.indicator {x} 1))
  simp_rw [e, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hwF : f w ∈ F := hF ⟨w, (Set.Finite.mem_toFinset hc).1 hw, rfl⟩
  simp only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq F (f w) (fun x => g x * c w), if_pos hwF, mul_comm]

theorem exists_finset_resCyc {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {q : Y ⟶ Sp k} (hq : IsAmb q) {B : LB Y} (hB : B.IsLB) (t : B.Sec) (z : Y) :
    ∃ F : Finset Y, ∀ F' : Finset Y, F ⊆ F' → ∀ g : Y → ℝ,
      resCyc hB t g z = ∑ x ∈ F', g x * resCyc hB t (Set.indicator {x} 1) z := by
  classical
  by_cases h : genericPoint (clo z) ∈ nonzeroLocus (secPull t (cloι z))
  · have : IsNoetherian (clo z) := (hq.sub (cloι z)).isNoetherian
    set D := divOfSec (LB.isLB_pull hB (cloι z)) _ h
    have hc : (Function.support fun w => (D.mult w : ℝ)).Finite :=
      D.finite_support_mult.subset fun w hw h0 => hw (by simp [h0])
    refine ⟨(hc.image fun w => cloι z w).toFinset, fun F' hF' g => ?_⟩
    simp only [resCyc, dif_pos h]
    refine finsum_mul_comp_eq_sum_indicator _ hc _ F' ?_ g
    intro y hy
    exact hF' ((Set.Finite.mem_toFinset _).2 hy)
  · refine ⟨∅, fun F' _ g => ?_⟩
    simp [resCyc, dif_neg h]

end GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem iterDiv_symm : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ (A B : LB Y) (hA : A.IsLB) (hB : B.IsLB) (s : A.Sec) (t : B.Sec) (hs : genericPoint Y ∈ nonzeroLocus s) (ht : genericPoint Y ∈ nonzeroLocus t), (∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → ∀ g : Y → ℝ, ∑ᶠ z, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t g z = ∑ᶠ z, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s g z := by
  intro k _ Y _ _ q hq A B hA hB s t hs ht hst g
  classical
  have : IsNoetherian Y := hq.isNoetherian
  choose Ft hFt using exists_finset_resCyc hq hB t
  choose Fs hFs using exists_finset_resCyc hq hA s
  have hms : (Function.support fun z => ((divOfSec hA s hs).mult z : ℝ)).Finite :=
    (divOfSec hA s hs).finite_support_mult.subset fun w hw h0 => hw (by simp [h0])
  have hmt : (Function.support fun z => ((divOfSec hB t ht).mult z : ℝ)).Finite :=
    (divOfSec hB t ht).finite_support_mult.subset fun w hw h0 => hw (by simp [h0])
  set F := hms.toFinset.biUnion Ft ∪ hmt.toFinset.biUnion Fs
  have Ls : ∀ h : Y → ℝ, ∑ᶠ z, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t h z =
      ∑ z ∈ hms.toFinset, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t h z := fun h =>
    finsum_eq_sum_of_support_subset _ fun z hz => by
      rw [Set.Finite.coe_toFinset]; exact left_ne_zero_of_mul hz
  have Lt : ∀ h : Y → ℝ, ∑ᶠ z, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s h z =
      ∑ z ∈ hmt.toFinset, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s h z := fun h =>
    finsum_eq_sum_of_support_subset _ fun z hz => by
      rw [Set.Finite.coe_toFinset]; exact left_ne_zero_of_mul hz
  have Es : ∑ z ∈ hms.toFinset, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t g z =
      ∑ x ∈ F, g x * ∑ z ∈ hms.toFinset, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t (Set.indicator {x} 1) z := by
    rw [Finset.sum_congr rfl fun z hz => by
      rw [hFt z F (Finset.subset_union_left.trans' (Finset.subset_biUnion_of_mem Ft hz)) g]]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have Et : ∑ z ∈ hmt.toFinset, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s g z =
      ∑ x ∈ F, g x * ∑ z ∈ hmt.toFinset, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s (Set.indicator {x} 1) z := by
    rw [Finset.sum_congr rfl fun z hz => by
      rw [hFs z F (Finset.subset_union_right.trans' (Finset.subset_biUnion_of_mem Fs hz)) g]]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [Ls, Lt, Es, Et]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Ls, ← Lt, GlobalTheory.T.finsum_mult_resCyc_indicator_symm' k Y q hq A B hA hB s t hs ht hst x]

end GlobalTheory.MixHt
