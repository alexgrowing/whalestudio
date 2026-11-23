import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.BcSumSingle
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.OmegaPullSCompRight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.Leaves
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraMapSecEq
open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

theorem UpperTheory.Gal.G3.jHOmega :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_equiv → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_forms → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_sections → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_affine → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_omega := by
  intro hE hF hS hA k k' _ _ _ J e X X' s s' g h a V hV
  letI := algΓ s
  letI := algΓ s'
  haveI : IsAffineHom g := hA k k' (algebraMap k k') X X' s s' g h
  have hV' : IsAffineOpen (g ⁻¹ᵁ V) := hV.preimage g
  have hForms : IsBC e (formPullS h.w V a) :=
    hF k k' J e _ _ _ (semiHom_appSecS h.w V) (hS k k' J e X X' s s' g h V hV) a
  refine hE k k' J e _ _ _ _ (formPullS h.w V a) (omSecEquiv s a ⟨V, hV⟩).symm
    (omSecEquiv s' a ⟨g ⁻¹ᵁ V, hV'⟩) _ (fun x ↦ ?_) hForms
  obtain ⟨y, rfl⟩ := (omSecEquiv s a ⟨V, hV⟩).surjective x
  rw [LinearEquiv.symm_apply_apply]
  exact omegaPullS_toOmega h.w a V y
