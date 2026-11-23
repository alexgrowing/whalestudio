import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LevelTrAAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PiTermEqTraceSumOfDegreeFourTest
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TraceUnique

namespace UpperTheory.V.Z.Mult.Pi

theorem minIdem_pf : MinIdem := by
  intro J M Y _ _ _ _ _ _ α a hs hk
  have surj : Function.Surjective (FreeAlgebra.lift ℂ α) :=
    DiscreteGroups.T1.Desc.Swap3.burnside (FreeAlgebra.lift ℂ α) fun W hW => hs W fun f x hx => by
      simpa using hW (FreeAlgebra.ι ℂ f) x hx
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hv
  obtain ⟨p, hp⟩ := surj (LinearMap.smulRight l v)
  have same : ∀ r r', FreeAlgebra.lift ℂ α r = FreeAlgebra.lift ℂ α r' →
      FreeAlgebra.lift ℂ a r = FreeAlgebra.lift ℂ a r' := by
    intro r r' h
    have h0 : FreeAlgebra.lift ℂ a (r - r') = 0 := hk _ (by rw [map_sub, h, sub_self])
    rw [map_sub] at h0
    exact sub_eq_zero.1 h0
  have idem : LinearMap.smulRight l v * LinearMap.smulRight l v = LinearMap.smulRight l v := by
    ext x
    simp [hl]
  refine ⟨p, ?_, ?_, fun q => ⟨l (FreeAlgebra.lift ℂ α q v), ?_⟩⟩
  · rw [hp, idem, LinearMap.trace_smulRight, hl]
  · rw [← map_mul]
    exact same _ _ (by rw [map_mul, hp, idem])
  · rw [← map_mul, ← map_mul, ← map_smul]
    refine same _ _ ?_
    rw [map_mul, map_mul, map_smul, hp]
    ext x
    simp [smul_smul, mul_comm]

end UpperTheory.V.Z.Mult.Pi
