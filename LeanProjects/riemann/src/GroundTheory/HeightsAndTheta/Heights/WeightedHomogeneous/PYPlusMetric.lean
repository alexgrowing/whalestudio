import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

theorem YPlusMetric.proof (hF : ChartFormsAlt.Statement) (hG : HomogGeneratorsExist.Statement)
    (hM : ChartMetric.Statement) (hP : ConePoints.Statement) : YPlusMetric.Statement := by
  intro ι _ _ n P D Ω _ y x' N hR hdeg hconj
  obtain ⟨d₀, hd₀⟩ := hF ι n P D
  obtain ⟨g, hg⟩ := hd₀ d₀ le_rfl
  obtain ⟨r, G, δ, hGen⟩ := hG ι n P
  obtain ⟨⟨H, hHdeg, hHmet, hHconj⟩, hval⟩ := hM ι n P D N hdeg d₀ g hg r G δ hGen
  refine ⟨H, hHdeg, hHconj hconj, ?_⟩
  intro j g' m dg dm hg' hm hdg hy z hz

  have hw : unflatCone z ∈ D.extPoints := by
    refine ⟨(blockNonzero_unflatCone_iff z).mpr hz.1, fun f hf ↦ ?_⟩
    rw [hR.ext_eq] at hf
    rw [← eval_map_flatCone, flatCone_unflatCone]
    exact hz.2 f hf
  obtain ⟨hold, la, _, hnew⟩ := (hP ι n P D d₀ g hg).2 _ hw
  have hev : ∀ f : MvPolynomial (Coord n) ℤ,
      evalCone (D.basePart₂ (unflatCone z)) f = eval (D.oldFlat z) (map (Int.castRingHom ℂ) f) := by
    intro f
    rw [← eval_map_flatCone]
    rfl

  have hex : ∀ k, ∃ i, D.basePart₂ (unflatCone z) k i ≠ 0 := fun k ↦ Function.ne_iff.mp (hold.1 k)
  choose c hc using hex
  have hmc : evalCone (D.basePart₂ (unflatCone z)) (chartMonomial c d₀) ≠ 0 := by
    rw [evalCone_chartMonomial]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
  have hlive : P.IsLive c := by
    intro k hk
    apply hc k
    have := hold.2 _ hk
    simpa [evalCone] using this

  have hdeg' : ∀ k, (dg k : ℤ) = dm k + D.deg k := fun k ↦ by
    rw [hdg k, ← hdeg]; rfl
  have h1 : P.mkF g' = D.elt j * P.mkF m :=
    ((hR.reads j) g' m dg dm ((geoMultiHomog_iff _ _).mp hg') ((geoMultiHomog_iff _ _).mp hm) hdeg').mp
      (by rw [hy, mul_comm])
  have hcross : chartMonomial c d₀ * g' - m * g c j ∈ P.ideal := by
    rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, h1, hg.value c hlive j]
    ring
  have hcz := hold.2 _ hcross
  rw [hev] at hcz
  simp only [map_sub, map_mul, sub_eq_zero] at hcz

  have hblk : BlockNonzero (unflatCone z) := (blockNonzero_unflatCone_iff z).mpr hz.1
  have hoblk : BlockNonzero (unflatCone (D.oldFlat z)) := hold.1
  have hHz : H.toGeo.h z = ‖la‖ * N.metric (D.basePart₂ (unflatCone z)) := by
    rw [HermLine.toGeo_h_of_blockNonzero _ hblk, hHmet _ hblk]
    exact hval _ hw c la hmc (hnew c hmc)
  rw [HermLine.toGeo_h_of_blockNonzero _ hoblk, hHz]
  have hzj : z ⟨none, j⟩ = la * evalCone (D.basePart₂ (unflatCone z)) (g c j) /
      evalCone (D.basePart₂ (unflatCone z)) (chartMonomial c d₀) := hnew c hmc j
  simp only [hev] at hzj hmc
  have key : z ⟨none, j⟩ * eval (D.oldFlat z) (map (Int.castRingHom ℂ) m) =
      la * eval (D.oldFlat z) (map (Int.castRingHom ℂ) g') := by
    rw [hzj, div_mul_eq_mul_div, div_eq_iff hmc]
    linear_combination (-la) * hcz
  have hnorm := congrArg (‖·‖) key
  simp only [norm_mul] at hnorm
  change _ = _ * (_ * N.metric (unflatCone (D.oldFlat z)))
  rw [hnorm]
  ring

end

end GroundTheory.Heights₂.Heights
