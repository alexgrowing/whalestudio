import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlagDomainModelsExponentsLevelM
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointsAllNormalisationsFamilyUnif
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUniformisationIsComplexUniformisation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArithmeticGroupCuspCentreLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspSectionAdelicLeftInvariantContinuousStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMemberDictionaryContextGoodEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDictionaryByMarkingRuleStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DictIsUnifOfMarkingRuleDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryInvariantRationalLevelStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryAdelicCharOfHeckeCharStatement

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem exists_pkgLaws : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → (∀ a, χ (idF D a) = 1) → ∃ un dict mu, C.IsDict dict ∧ GlobalTheory.FrameUnif.FramesOK C.e C.F C.M un ∧ PkgLaws V C.hr C.ι Kf χ (C.unf un) dict mu C.x₀ := by
  intro D H Dw l Xo c σ V r C hC Kf hK χ hχ hχF
  have hS := GlobalTheory.firstFiveLaws.1.secBaseChange
  have hT := GlobalTheory.firstFiveLaws.2.1.secTwist
  have hneg : GlobalTheory.FrameUnif.NegXi C.M :=
    (GlobalTheory.T.exists_memberDictionaryContext_goodEmbedding D H Dw l Xo c σ V r C.hr C.ι hC.iota hC.pos hC.lA hC.good).2.1 C hC
  obtain ⟨un, hun⟩ := GlobalTheory.FrameUnif.exists_framesOK hS hT _ H Dw l Xo c σ C.g C.e C.F r C.M hC.good hC.base hneg
  obtain ⟨dict, hd⟩ := GlobalTheory.T.exists_dictionary_by_marking_rule D H Dw l Xo c σ V r C hC
  obtain ⟨mu, hval, hmul, hnorm, hrat, hcont⟩ := GlobalTheory.T.exists_unitaryAdelicChar_of_heckeChar D V χ hχ hχF
  have hU := GlobalTheory.FrameUnif.isUnf_built hS _ H Dw l Xo c σ C.g C.e C.F r C.M un hC.good hC.base hneg hun
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  refine ⟨un, dict, mu, hd, hun, ?_⟩
  refine
    { unf := (Formalism.L2.PjFree.isUnf_ofPj (C.unf un)).1 hU
      unTest := fun k x => GlobalTheory.Frames.allTest_of_secBaseChange hS _ H Dw l Xo c (CAt σ) (un k x)
      chi1 := hC.base.chi
      modelW := hC.modelW
      familyUniformisationBasePointOrthogonal := hC.orth
      muUnit := ⟨hmul, hnorm, hrat, (GlobalTheory.T.memberDictionary_invariant_rational_level D H Dw l Xo c σ V r C hC dict hd Kf hK).2.2.2.1⟩
      muCont := hcont
      muVal := hval
      adelAut := GlobalTheory.T.cuspSection_adelic_leftInvariant_continuous D H Dw l Xo c σ V r C hC dict hd mu hmul hrat hcont
      expo := fun ρ => ⟨GlobalTheory.CuspCentre.latZ _ r ρ _ C.M.X,
        GlobalTheory.ExpoModels.expoMatch_models _ H Dw l Xo _ C.g _ C.F r C.M ρ hC.base hC.lA⟩
      dictLaws := ⟨C.g, C.e, C.F, id, C.M.φ, C.th, fun _ τ => hC.inf τ.1,
        GlobalTheory.T.dictIsUnif_of_markingRule_dictionary D H Dw l Xo c σ V r C hC dict hd Kf hK, ⟨hC.base.ef, fun k x => ?_⟩, fun h => ?_⟩ }
  · obtain ⟨Pm, h1, h2, h3, h4, -⟩ := hun.1 k x
    exact ⟨Pm, h1, h2, h3, h4⟩
  · obtain ⟨γ, ⟨h1, h2, h3⟩, h4⟩ := hd.1 h
    refine ⟨γ, h1, h2, h3, fun τ => ?_⟩
    exact congrFun h4 τ

end GlobalTheory.Member
