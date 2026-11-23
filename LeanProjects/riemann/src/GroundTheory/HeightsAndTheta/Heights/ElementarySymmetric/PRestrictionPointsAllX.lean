import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.HypsFurther
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinRestrictionPoints
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)
open IndefiniteRowSideFullHecke.Kleiman2 (locIn modelPts modVec resImage residue ResField)

theorem RestrictionPointsAll.proof : RestrictionPointsAll.Statement := by
  intro S _ K ι Ω _ _ y c p _ hc
  ext z'
  constructor
  · rintro ⟨c₁, hv, P, hP, rfl⟩
    obtain ⟨hz, heq⟩ := RestrictionPoints.main y c p hc c₁ hv P
    exact ⟨_, ⟨c₁, fun k => RestrictionPoints.ne_zero_of_modVec_ne_zero y c p (hv k), _,
      Ideal.comap_isPrime _ _, rfl⟩, hz, heq.symm⟩
  · rintro ⟨_, ⟨c₁, hc₁, q, hq, rfl⟩, hz, rfl⟩
    have hA : ∀ x ∈ chartRingOver S y c₁, x ∈ locIn (chartRingOver S y c) p :=
      fun x hx => hz (RestrictionPoints.mem_locIn_of_mem _ q hx)
    have hv : ∀ k, modVec S y c p ⟨k, c₁ k⟩ ≠ 0 := by
      intro k
      have h1 := RestrictionPoints.mem_locIn_of_mem (chartRingOver S y c) p
        (RestrictionPoints.ratio_mem y c ⟨k, c₁ k⟩)
      rw [← RestrictionPoints.resMap_ratio y c p ⟨k, c₁ k⟩ h1]
      refine RestrictionPoints.resMap_ne_zero_of_inv y c p h1 (div_ne_zero (hc₁ k) (hc k)) ?_
      rw [inv_div]
      exact hA _ (RestrictionPoints.ratio_mem y c₁ ⟨k, c k⟩)
    have hker : RingHom.ker (RestrictionPoints.chartRes y c p hc c₁ hv) ≤ q := by
      intro b hb
      by_contra hbq
      have hb0 : (b : Ω) ≠ 0 := coe_ne_zero_of_notMem y c₁ q hbq
      have hbi : (b : Ω)⁻¹ ∈ locIn (chartRingOver S y c₁) q :=
        (mem_locIn_chart_iff y c₁ q).mpr ⟨1, b, hbq, by simp⟩
      apply RestrictionPoints.resMap_ne_zero_of_inv y c p (hA b b.2) hb0 (hz hbi)
      exact congrArg Subtype.val (RingHom.mem_ker.mp hb)
    have hsurj := RestrictionPoints.chartRes_surjective y c p hc c₁ hv
    have hP : (q.map (RestrictionPoints.chartRes y c p hc c₁ hv)).IsPrime :=
      Ideal.map_isPrime_of_surjective hsurj hker
    have hcq : (q.map (RestrictionPoints.chartRes y c p hc c₁ hv)).comap
        (RestrictionPoints.chartRes y c p hc c₁ hv) = q := by
      rw [Ideal.comap_map_of_surjective _ hsurj]
      exact sup_eq_left.mpr hker
    obtain ⟨-, heq⟩ := RestrictionPoints.main y c p hc c₁ hv
      (q.map (RestrictionPoints.chartRes y c p hc c₁ hv))
    rw [hcq] at heq
    exact ⟨c₁, hv, _, hP, heq⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
