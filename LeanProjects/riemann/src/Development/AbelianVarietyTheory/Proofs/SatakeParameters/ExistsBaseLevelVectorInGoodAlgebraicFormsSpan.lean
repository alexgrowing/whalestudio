import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeakStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsFormsOnRankSpaceNormalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelVectorGoodTypeStableSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodFormsBaseLevelIffGoodProjectionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodProjectorUnitaryFormsModelLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3

theorem exists_part_level_vector : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → ∀ j c, R.Wc' j c ≠ ⊥ → ∃ w ∈ R.Wc' j c, w ≠ 0 ∧ w ∈ R.toRealDat.WS F.lv2 false j (sg0 D A3.A) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hW hEx hSch s hOk hGG hU j c hne
  obtain ⟨hCoreF, hSF, -, -, -, hWc, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hW
  have hCore := hCoreF hEx
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨h, -, -, -, hsup, hstab, -, -⟩ := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hCore hSch hX R.SF hSF j
  obtain ⟨hid, -, -, -⟩ := eH_laws R.toRealDat F.lv2 hCore hX j
  have hfix : ∀ u ∈ Wcc R.toRealDat R.SF j c, eH R.toRealDat j u = u := by
    intro u hu
    have hr : u ∈ LinearMap.range (eH R.toRealDat j) := hsup ▸ (le_iSup (fun c => Wcc R.toRealDat R.SF j c) c) hu
    obtain ⟨x, rfl⟩ := hr
    rw [← Module.End.mul_apply, hid]
  rw [hWc] at hne ⊢
  obtain ⟨u, huU, hu0, hup⟩ := GlobalTheory.T.exists_level_vector_goodType_stable_subspace (sg0 D A3.A) A3.A.X F.P0 F.ψ0⁻¹ (R.gW j (sg0 D A3.A))
    (Wcc R.toRealDat R.SF j c) hX hGG (fun g => hstab c g) hne (fun u hu => by
      have := hfix u hu
      simpa [eH, RealDat.eC] using this)
  refine ⟨u, huU, hu0, ?_⟩
  have hlev := (GlobalTheory.T.goodForms_baseLevel_iff_goodProjection R.toRealDat F.lv2 hCore hX j u).2 ⟨hfix u huU, hup⟩
  have hL := GlobalTheory.LevelForms.levelW_of_irr R.toRealDat F.lv2 hX hU hCore.models.HW
  rw [hL false j (sg0 D A3.A)]
  exact hlev

end GlobalTheory.Hk3
