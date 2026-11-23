import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveVertIndexSteps
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLogCardLength
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveDivVertical
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalAmple
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace CurveVerticalIndex

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem span_toAddSubgroup (y : (Σ k, ι k) → Ω) (x : Ω) :
    (Submodule.span (curveRing y) {x}).toAddSubgroup = curveMul y x := by
  ext z
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton, curveMul, AddSubgroup.mem_map,
    AddMonoidHom.coe_mulLeft, Subring.mem_toAddSubgroup]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, b.2, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩

omit [∀ k, Fintype (ι k)] in

theorem genIndex_eq_card (y : (Σ k, ι k) → Ω) (a : K → ℤ) {x : Ω} (hx : x ∈ curveSectionMod y a) :
    genIndex (chartLat y a 1) (curveMul y x) = Nat.card (curveSectionQuot y a x) := by
  have hle : curveMul y x ≤ chartLat y a 1 := by
    rw [← span_toAddSubgroup]
    intro z hz
    exact (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)) hz
  rw [genIndex, AddSubgroup.relIndex_eq_one.mpr hle, Nat.cast_one, div_one, ← span_toAddSubgroup]
  rfl

end CurveVerticalIndex

theorem CurveVertIndex.proof (hF : CurveSectionQuotFinite.Statement) (hV : CurveVertPointLength.Statement)
    (hR : CurveVertPointResidue.Statement) : CurveVertIndex.Statement := by
  intro K _ ι _ Ω _ y s d hP hs hsP
  have := hF K ι Ω y s d hP hs hsP
  obtain ⟨hbij, hmult⟩ := hV K ι Ω y s d hP hs hsP
  rw [CurveVerticalIndex.genIndex_eq_card y _ (HilbertSamuel.LiftBirationalAmple.chartLat_form hs),
    LogCardLength.proof (curveRing y) (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)), vertR]
  calc _ = ∑ᶠ W ∈ divSupp (mCoordIdeal y) s,
          (locLen (curvePtIdeal y W) (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) : ℝ) *
            Real.log (Nat.card (curveRing y ⧸ curvePtIdeal y W)) := by
        refine finsum_mem_congr rfl fun W hW => ?_
        rw [if_neg (IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical.full K ι _ s d hP hs hsP W hW), hmult W hW,
          ← hR K ι Ω y s d hP hs hsP W hW]
        congr 3
    _ = ∑ᶠ m ∈ {m : Ideal (curveRing y) |
          m.IsMaximal ∧ locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) ≠ 0},
          (locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) : ℝ) *
            Real.log (Nat.card (curveRing y ⧸ m)) :=
        finsum_mem_eq_of_bijOn _ hbij fun _ _ => rfl
    _ = _ := by
        refine finsum_mem_inter_support_eq _ _ {m : Ideal (curveRing y) | m.IsMaximal} ?_
        ext m
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support]
        exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, fun h0 => h2 (by simp [h0])⟩, h2⟩⟩

end

end GroundTheory.Heights₂.Heights.Targets
