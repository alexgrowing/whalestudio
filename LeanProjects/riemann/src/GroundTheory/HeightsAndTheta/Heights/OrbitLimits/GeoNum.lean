import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers

noncomputable section

namespace GeoNumTarget

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem geoIsMultiProjPrime {F : Type} [Field F] {P : Ideal (NumbersDVR.MRing ι F)}
    (hP : NumbersDVR.IsMultiProjPrime P) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime P :=
  ⟨hP.isPrime, (VocabMultiHomogIdeal.proof VocabMultiHomog.proof F K ι P).2 hP.multiHomog,
    hP.relevant⟩

theorem dvrIsMultiProjPrime {F : Type} [Field F] {P : Ideal (NumbersDVR.MRing ι F)}
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime P) : NumbersDVR.IsMultiProjPrime P :=
  ⟨hP.1, (VocabMultiHomogIdeal.proof VocabMultiHomog.proof F K ι P).1 hP.2.1, hP.2.2⟩

theorem finsum_mul_eq_sum {α : Type*} (D : α →₀ ℤ) (J : α → ℤ) :
    ∑ᶠ W, D W * J W = D.sum fun W m => m * J W := by
  classical
  rw [Finsupp.sum, finsum_eq_sum_of_support_subset]
  intro W hW
  rw [Function.mem_support] at hW
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h0
  exact hW (by rw [h0, zero_mul])

theorem isIntersectionTheory {F : Type} [Field F] (I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily F ι)
    (hI : ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I) :
    IsIntersectionTheory F (fun P n L => I P n L) where
  base := by
    intro P hP hdim
    have hd : ringKrullDim (NumbersDVR.MRing ι F ⧸ P) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞) :=
      (CutRegular.relDim_eq_natCast_iff P 0).mp (by rw [hdim]; rfl)
    have hi : ∀ k, (X ⟨k, (hP.relevant k).choose⟩ : NumbersDVR.MRing ι F) ∉ P :=
      fun k => (hP.relevant k).choose_spec
    rw [hI.1 P ![] (fun k => (hP.relevant k).choose) ⟨geoIsMultiProjPrime hP, hd⟩ hi,
      ← NumbersDVR.IntNumPoint.proof IntNumBase.full F K ι P _ hP hd hi]
    obtain ⟨-, h⟩ := IntNumBase.full F K ι P hP hdim
    rw [h]
    have := hP.isPrime
    simp [resDeg, hP.isPrime]
  cut := by
    intro P n hP hdim bf bg f g hf hg hfP hgP bs
    have hd := (CutRegular.relDim_eq_natCast_iff P (n + 1)).mp hdim
    have key := hI.2 P n bs (fun k => (bf k : ℤ) - bg k) f g ⟨geoIsMultiProjPrime hP, hd⟩
      ⟨bf, bg, (VocabMultiHomog.proof F K ι f bf).2 hf, (VocabMultiHomog.proof F K ι g bg).2 hg,
        hfP, hgP, fun k => rfl⟩
    refine key.trans ?_
    have hD : ∀ W, NumbersDVR.ratDiv P f g W = ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv P f g W := by
      intro W
      simp only [NumbersDVR.ratDiv, ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv, Finsupp.sub_apply,
        Finsupp.mapRange_apply]
      rw [VocabDivCycle.proof F K ι P f W, VocabDivCycle.proof F K ι P g W]
    simp only [NumbersDVR.cycEval, ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval, hD]
    exact (finsum_mul_eq_sum _ _).symm

theorem isFieldIntersection_intNum (p : ℕ) [Fact p.Prime] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection (F := ZMod p) (ι := ι)
      (fun V _ L => NumbersDVR.intNum (ZMod p) V L) :=
  IntNumIsFieldIntersection.full (ZMod p) K ι

end GeoNumTarget

open GeoNumTarget Bridge.GeoNum in

theorem geoNumStatement {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.GeoNumStatement ι := by
  classical
  intro p _ I hI V n a hV hpV hproj
  have hker : RingHom.ker (red (ι := ι) p) ≤ V := by
    rw [ker_red, Ideal.span_le, Set.singleton_subset_iff]
    rw [map_natCast]
    exact hpV
  have hcm : (V.map (red p)).comap (red p) = V := comap_map_eq p hker
  have hdim : ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι ⧸ V) =
      ((n + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [← hproj.2]
    have := ringKrullDim_eq_of_ringEquiv (quotEquiv p (V.map (red p)))
    rw [hcm] at this
    exact this
  have hC : (C (p : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) ∈ V := by
    rw [map_natCast]
    exact hpV
  rw [← Bridge.intNum_map_eq_geoNum p n V hV hC hdim a]
  exact (IntNumUnique.full (ZMod p) K ι _ (isIntersectionTheory I hI) _
    (dvrIsMultiProjPrime hproj.1) n ((CutRegular.relDim_eq_natCast_iff _ n).mpr hproj.2) a).symm

end

end GroundTheory.Heights₂.Heights
