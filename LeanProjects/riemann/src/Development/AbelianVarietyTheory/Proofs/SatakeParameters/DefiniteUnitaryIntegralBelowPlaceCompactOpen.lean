import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOfNotApartOfNotSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenSubgroupCharacterKernel
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev

noncomputable section

namespace GlobalTheory.Cong.AdaptLev

open GlobalTheory.BCT.GlobLev GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem finPart_mem_integral_iff (k : finU E a) :
    finPart E a k ∈ AdelicGLn.integralFiniteGL E a ↔ ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u a := by
  rw [AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
  simp only [mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles]
  exact ⟨fun h u => ⟨fun i j => h.1 i j u, fun i j => h.2 i j u⟩,
    fun h => ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩⟩

theorem isOpen_KGL (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) :
    IsOpen (GlobalTheory.LFun.KGL w a : Set (GL (Fin a) (w.adicCompletion E))) := by
  have hK := GlobalTheory.SmGL.SphCompletion.KO_completion (F := E) w a
  have h : IsOpen (GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin a) : Set (GL (Fin a) (w.adicCompletion E))) :=
    GlobalTheory.SplitFlip.isOpen_KO
  rwa [hK] at h

theorem isClosed_KGL (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) :
    IsClosed (GlobalTheory.LFun.KGL w a : Set (GL (Fin a) (w.adicCompletion E))) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_KGL w a)

theorem mem_intU_iff_of_mem_locU {w : HeightOneSpectrum (𝓞 E)} {x : UA E a} (hx : x ∈ locU a w) :
    x ∈ intU a w ↔ cLoc w x ∈ GlobalTheory.LFun.KGL w a :=
  ⟨fun h => (mem_intU.1 h).2 w (fun h' => h' rfl), mem_intU_of hx⟩

theorem isOpen_intU (w : HeightOneSpectrum (𝓞 E)) :
    IsOpen (((intU a w).subgroupOf (locU a w)) : Set (locU a w)) := by
  have e : (((intU a w).subgroupOf (locU a w)) : Set (locU a w)) =
      (fun x : locU a w => cLoc w x.1) ⁻¹' (GlobalTheory.LFun.KGL w a : Set _) := by
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
    exact mem_intU_iff_of_mem_locU x.2
  rw [e]
  exact (isOpen_KGL w a).preimage ((continuous_cLoc w).comp continuous_subtype_val)

theorem isCompact_intU (w : HeightOneSpectrum (𝓞 E)) :
    IsCompact (intU a w : Set (UA E a)) := by
  haveI : ∀ u : HeightOneSpectrum (𝓞 E), T2Space (GL (Fin a) (u.adicCompletion E)) :=
    fun _ => Units.isEmbedding_embedProduct.t2Space
  let T : Set (finU E a) := {x | x.1 ∈ intU a w}
  have hK0 : IsCompact {x : finU E a | ((x : UA E a) : GA E a) ∈
      finGL E a '' (AdelicGLn.integralFiniteGL E a : Set _)} :=
    isClosedEmbedding_finU.isCompact_preimage
      ((AdelicGLn.isCompact_integralFiniteGL E a).image continuous_finGL_ad)
  have hTsub : T ⊆ {x : finU E a | ((x : UA E a) : GA E a) ∈
      finGL E a '' (AdelicGLn.integralFiniteGL E a : Set _)} := by
    intro x hx
    have hx' := mem_intU.1 hx
    have hall : ∀ u, cLoc u x.1 ∈ GlobalTheory.LFun.KGL u a := by
      intro u
      by_cases hu : Apart u w
      · rw [((GlobalTheory.Cong.LevelExt.mem_locU_iff x.1).1 hx'.1).2 u hu]
        exact one_mem _
      · exact hx'.2 u hu
    refine ⟨finPart E a x, (finPart_mem_integral_iff x).2 hall, ?_⟩
    have h1 : Matrix.GeneralLinearGroup.map (pInf E) ((x : UA E a) : GA E a) = 1 := x.2
    exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)
  have hTe : T = (⋂ u, ⋂ (_ : Apart u w), {x : finU E a | cLoc u x.1 = 1}) ∩
      ⋂ u, ⋂ (_ : ¬ Apart u w), {x : finU E a | cLoc u x.1 ∈ GlobalTheory.LFun.KGL u a} := by
    ext x
    simp only [T, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, mem_intU,
      GlobalTheory.Cong.LevelExt.mem_locU_iff]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨x.2, h.1⟩, h.2⟩⟩
  have hTc : IsClosed T := by
    rw [hTe]
    refine (isClosed_iInter fun u => isClosed_iInter fun _ => ?_).inter
      (isClosed_iInter fun u => isClosed_iInter fun _ => ?_)
    · exact isClosed_eq ((continuous_cLoc u).comp continuous_subtype_val) continuous_const
    · exact (isClosed_KGL u a).preimage ((continuous_cLoc u).comp continuous_subtype_val)
  have hT := (hK0.of_isClosed_subset hTc hTsub).image continuous_subtype_val
  have e : Subtype.val '' T = (intU a w : Set (UA E a)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hy
      exact ⟨⟨y, ((GlobalTheory.Cong.LevelExt.mem_locU_iff y).1 (intU_le_locU w hy)).1⟩, hy, rfl⟩
  rwa [e] at hT

theorem intU_isCompact_isOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsCompact (GlobalTheory.Cong.AdaptLev.intU a w : Set (UA E a)) ∧ IsOpen (((GlobalTheory.Cong.AdaptLev.intU a w).subgroupOf (locU a w)) : Set (locU a w)) :=
  fun _ _ _ _ _ w => ⟨isCompact_intU w, isOpen_intU w⟩

end GlobalTheory.Cong.AdaptLev
