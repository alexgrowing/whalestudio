import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamGlobalFormsBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupSelfZeroDeRhamAbelianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToStructureH1SurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfFormInjectiveOfH0Const
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperH2ExteriorSquareIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianStructureCohomologyStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsProjectiveRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamH1RankPrimitiveStatement

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem abelianHodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham := by
  intro R _ A _ g hA hg
  obtain ⟨hfr, h0, -, -⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hg
  obtain ⟨hO, hW, hB1, -⟩ := GlobalTheory.T.abelian_structure_cohomology_statement R A g hA hg
  have hcl := GlobalTheory.T.abelianScheme_globalOneForms_closed R A g hA hg
  have hs := GlobalTheory.T.de_rham_to_structure_h1_surjective R A g hA hg
  have hH := (GlobalTheory.T.de_rham_h1_rank_primitive R A g hA hg).1
  refine ⟨⟨hH.1, hH.2.1, fun p ↦ (hH.2.2 p).trans (by push_cast; rfl)⟩,
    GlobalTheory.T.hyper_h2_exterior_square_iso R _ (OAff A.hom) hfr h0 hcl hs hW (GlobalTheory.T.cup_self_zero_de_rham_abelian R A g hA hg),
    GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R A g hA hg, hO, ⟨hcl, ofForm_injective_of_H0Const R _ (OAff A.hom) h0, hs⟩, ?_⟩
  intro R' _ _ X' s' φ h
  obtain ⟨⟨e₁, he₁⟩, e₂, he₂⟩ := GlobalTheory.T.de_rham_global_forms_base_change R A g hA hg R' X' s' φ h
  obtain ⟨e₃, he₃⟩ := hB1 R' X' s' φ h
  refine ⟨⟨e₁, fun c ↦ ?_⟩, ⟨e₂, fun c ↦ ?_⟩, e₃, fun c ↦ ?_⟩
  · rw [he₁]; exact isPull1_pullHH1 h.w c
  · rw [he₂]; exact isPullForm_pullForm h.w c
  · rw [he₃]; exact isPullO_pullHO1 h.w c

end GlobalTheory.AbCoh
