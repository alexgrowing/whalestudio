import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenChartAffineOpenWithinStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenbundleFrameAffineAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenbundleFrameAffineAtlasIsFlagFrameCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProperNormalFlagSchemeOfAffineCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellsFramesTriangularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellFramesLastStepEigenmodulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseFlagBundlePreimageModuliStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointsEqOfSameStepsLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecHomExtOfLocalizationsAtAllPrimesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagCellContainingFramedPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagBundlePointCarryingOfLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatToSpecFieldStatement
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

theorem nonempty_flagModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension Dw.dim Y.s → PushInvertible Y.t.G Y.t.PP.L → Nonempty (GlobalTheory.FlagMod.FlagModel Y) := by
  intro E _ _ _ H Dw l Xo c Y _ hP
  obtain ⟨p⟩ := LowRank.nonempty_proj_id (E := E) (c := c)
  obtain ⟨A⟩ := GlobalTheory.T.exists_eigenbundleFrameAffineAtlas E H Dw l Xo c Y p hP
  have := A.fin
  obtain ⟨Z, π, g, κ, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.exists_proper_normal_flagScheme_of_affine_cover c.F Y.X Y.s (E →+* ℂ) Dw.mult A.N A.B A.V A.alpha A.cv A.Dv Y.proj Y.normal (GlobalTheory.T.eigenbundleFrameAffineAtlas_isFlagFrameCover E H Dw l Xo c Y p A) A.cov
  have hZ : Cells A π g κ := ⟨h1, h2, h3, h5, h6⟩
  have := h4
  have ht := GlobalTheory.T.flagCellFrameChangeTriangular_of_cells E H Dw l Xo c Y p A Z π g κ hZ
  have huniq : ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (P₁ : FrPt Xo c S') (z₁ z₂ : Sp S' ⟶ Z), (cellFrames hZ ht).Lies z₁ P₁ → (cellFrames hZ ht).Lies z₂ P₁ → z₁ = z₂ := by
    intro S' _ _ P₁ z₁ z₂ e₁ e₂
    refine GlobalTheory.T.spec_hom_ext_of_localizations_at_all_primes S' Z z₁ z₂ fun q => ?_
    obtain ⟨P', hP'⟩ := exists_frMap (IsScalarTower.toAlgHom c.F S' (Localization.AtPrime q.asIdeal)) P₁
    have l₁ := e₁.frMap hP'
    have l₂ := e₂.frMap hP'
    refine GlobalTheory.T.flagBundle_points_eq_of_same_steps_localRing E H Dw l Xo c Y p A Z π g κ hZ ht _ _ _ _ l₁.1 l₂.1 fun σ i => ?_
    obtain ⟨k, hk⟩ := exists_chart_of_isLocalRing (cellFrames hZ ht).cover (spMap (algebraMap S' (Localization.AtPrime q.asIdeal)) ≫ z₁)
    obtain ⟨k', hk'⟩ := exists_chart_of_isLocalRing (cellFrames hZ ht).cover (spMap (algebraMap S' (Localization.AtPrime q.asIdeal)) ≫ z₂)
    exact (l₁.initSpan_eq hk l₁.1 rfl σ i).symm.trans (l₂.initSpan_eq hk' l₂.1 rfl σ i)
  refine ⟨{ YY := Z, π := π, proper := h1, normal := h2, flat := ?_, F := cellFrames hZ ht
            dense := GlobalTheory.T.dense_flagBundle_preimage_moduli E H Dw l Xo c Y p A Z π g κ hZ, top := GlobalTheory.T.flagCellFrames_lastStep_eigenmodules E H Dw l Xo c Y p A Z π g κ hZ ht
            rep := fun S _ _ P => ?_, fin := fun K _ _ z => ?_ }⟩
  · exact GlobalTheory.T.flat_to_spec_field' c.F Z (π ≫ Y.s)
  · obtain ⟨z, hz⟩ := GlobalTheory.T.exists_flagBundle_point_carrying_of_local E H Dw l Xo c Y p A Z π g κ hZ ht S P huniq fun q => GlobalTheory.T.exists_flagCell_containing_framed_point E H Dw l Xo c Y p A Z π g κ hZ ht S P q
    exact ⟨z, hz, fun z' hz' => huniq S P z' z hz' hz⟩
  · refine (Set.finite_singleton z).subset fun z' ⟨hx, h⟩ => ?_
    exact GlobalTheory.T.flagBundle_points_eq_of_same_steps_localRing E H Dw l Xo c Y p A Z π g κ hZ ht K z' z _ hx rfl h

end GlobalTheory.FlagMod.FieldFlag
