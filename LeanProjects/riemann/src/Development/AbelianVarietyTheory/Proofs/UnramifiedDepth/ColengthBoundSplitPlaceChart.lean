import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MapPderiv
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsNilpotentGroupChartSmoothCommGroupStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLinearDataOfSplitFormalGroupExtensionStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.UniformizationSplitFormalGroupLawEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsHodgeTateDatumPolarisedAbelianCharactersStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ColengthBoundSplitPlaceLinearDataStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupActionLinearPartRingHomStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupLawJacobianExtensionChangeCoeffStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NilChartOfIsChartJStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPowerSeriesReadingGroupHomNilpotentChartsStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

theorem colength_bound_split_place_chart : ∀ (p : ℕ) [Fact p.Prime], AvFSt p := by
  intro p _ T _ _ _ _ _ _ hpT G _ _ D A U d F x hx OE _ _ _ _ _ _ _ io oD oA hlin act hact
    C _ _ _ v O _ _ hv _ _ _ iota hiota w t vd hvd rp rm W hW hW'
  obtain ⟨X, hX, hXr⟩ := GlobalTheory.T.exists_nilChart_reads_of_isChartJ T G U.smooth d F x hx
  have hread := hXr OE io act hact
  obtain ⟨FB, XB, hXB⟩ := GlobalTheory.T.exists_nilpotentGroupChart_smooth_commGroup T D.toPre.P.A D.toPre.P.g D.toPre.P.smoothDim
  have hαB : ∀ a : OE, ∃ φ : Fin D.toPre.P.g → PS T 1 D.toPre.P.g, Reads XB XB (oD.onB.act a) φ :=
    fun a => GlobalTheory.T.exists_powerSeries_reading_groupHom_nilpotentCharts T D.toPre.P.A D.toPre.P.A _ _ FB.F FB.F XB XB hXB hXB _ (oD.onB.hom a)
  choose αB hαB using hαB
  obtain ⟨r, J, Q, hext, heq⟩ := GlobalTheory.T.uniformization_split_formal_group_law_equivariant T _ D A G U d _ F FB X XB hX hXB
  obtain ⟨N, hN⟩ := heq OE io oD oA hlin act.act αB hread hαB
  obtain ⟨hlaw, hlinm, hextm⟩ := GlobalTheory.T.formalGroupLaw_jacobian_extension_changeCoeff T O iota
  obtain ⟨F', hF'⟩ := hlaw d F
  obtain ⟨FB', hFB'⟩ := hlaw _ FB
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.formalGroupAction_linearPart_ringHom T d F OE act O iota
  have hext' := hextm d _ r F FB J Q hext
  have hFH : FH p F'.F := by
    intro k
    rw [hF']
    obtain ⟨h1, h2, -, h4⟩ := GlobalTheory.FormalTorsion.fhSt p T hpT G D A U d F x hx C v O hv iota hiota k
    exact ⟨h1, h2, h4⟩
  have hB := GlobalTheory.T.exists_hodgeTateDatum_polarisedAbelian_characters p C v O hv T iota D.toPre.P _ rfl OE oD.onB FB XB hXB αB hαB
  rw [← hF', ← hFB'] at hext'
  rw [← hFB'] at hB
  obtain ⟨cp, hS, H, B, m, u, hu, hL⟩ := GlobalTheory.T.exists_linearData_of_split_formalGroup_extension p C v O hv OE d _ r F' FB' _ _ hext' hFH ρ N
    (fun a j => MvPowerSeries.map iota (αB a j))
    (fun a => by
      rw [hlinm, hlinm, (hρ a).2, ← Matrix.map_mul, ← Matrix.map_mul, (hN a).1])
    (fun a => by
      rw [hlinm, (hρ a).2, ← Matrix.map_mul, (hN a).2, Matrix.map_mul, Matrix.map_map]
      congr 2
      funext z
      simp) hB
  have hρf : (ρ : OE → Matrix (Fin d) (Fin d) O) = fun a => linPart (actMap iota act a) :=
    funext fun a => (hρ a).1
  obtain ⟨xs, hxs, hle⟩ := GlobalTheory.T.colength_bound_split_place_linear_data p C v O hv OE cp hS _ H d r m _ B ρ N _ hL w t vd hvd rp rm W
    (fun j => by rw [hρf]; exact (isEigBasis_iff _ _ _).1 (hW j))
    (fun τ hτ => by
      obtain ⟨W', h⟩ := hW' τ hτ
      exact ⟨W', by rw [hρf]; exact (isEigBasis_iff _ _ _).1 h⟩)
  refine ⟨xs, fun j => ⟨m, u, fun k => ?_, hxs j⟩, hle⟩
  rw [← hF']
  exact hu k

end GlobalTheory.ChF
