import Mathlib
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

open scoped Pointwise

noncomputable section

namespace GlobalTheory.Cong.LevAway

open Matrix GlobalTheory.PRep Formalism.UG GlobalTheory.BCT GlobalTheory.SplitPts GroundTheory.Automorphic GlobalTheory.BCT.GlobLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem integral_iff (x : UA E a) :
    GeneralLinearGroup.map (pFin E) (x : GA E a) ∈ AdelicGLn.integralFiniteGL E a ↔
      ∀ u, cLoc u x ∈ GlobalTheory.LFun.KGL u a := by
  rw [AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
  simp only [mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles]
  exact ⟨fun h u => ⟨fun i j => h.1 i j u, fun i j => h.2 i j u⟩,
    fun h => ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩⟩

theorem exists_compact_integral : ∃ C : Set (UA E a), IsCompact C ∧
    ∀ x ∈ finU E a, (∀ u, cLoc u x ∈ GlobalTheory.LFun.KGL u a) → x ∈ C := by
  let Kf : Subgroup (finU E a) := (AdelicGLn.integralFiniteGL E a).comap (finPart E a)
  have hO : IsOpen (Kf : Set (finU E a)) := (AdelicGLn.isOpen_integralFiniteGL E a).preimage continuous_finPart
  have hc : IsCompact (Kf : Set (finU E a)) := by
    refine IsCompact.of_isClosed_subset (isClosedEmbedding_finU.isCompact_preimage
      ((AdelicGLn.isCompact_integralFiniteGL E a).image continuous_finGL_ad))
      (Subgroup.isClosed_of_isOpen _ hO) fun x hx => ⟨finPart E a x, hx, ?_⟩
    have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E a) : GA E a) = 1 := x.2
    exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)
  refine ⟨Subtype.val '' (Kf : Set (finU E a)), hc.image continuous_subtype_val, fun x hx hi => ⟨⟨x, hx⟩, ?_, rfl⟩⟩
  exact (integral_iff x).2 hi

theorem exists_loc (w : HeightOneSpectrum (𝓞 E)) : ∃ f : UA E a → UA E a, Continuous f ∧
    ∀ x, f x ∈ locU a w ∧ cLoc w (f x) = cLoc w x := by
  by_cases hw : IsSplitAt w
  · obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
    refine ⟨fun x => (e.symm (cLoc w x)).1, continuous_subtype_val.comp (e.symm.continuous.comp (continuous_cLoc w)),
      fun x => ⟨(e.symm _).2, ?_⟩⟩
    rw [← he]; exact e.apply_symm_apply _
  · have hc : conjSrc (conjE E) w = w := conjSrc_eq_of_not_split hw
    have key : ∀ x : UA E a, finGL E a (locGL E a w (cLoc w x)) ∈ UA E a := by
      intro x
      refine finGL_mem_UA _ fun u => ?_
      by_cases hu : u = w
      · subst hu
        have e1 : ∀ v, v = u → GeneralLinearGroup.map (pLoc E v) (locGL E a u (cLoc u x)) = cLoc v x := by
          rintro v rfl; exact pLoc_locGL _ _
        rw [e1 _ hc, e1 u rfl]
        exact comp_eq x u
      · have h3 : conjSrc (conjE E) u ≠ w := fun e => hu (by rw [← conjSrc_conjSrc_cm u, e, hc])
        rw [pLoc_locGL_of_ne hu, pLoc_locGL_of_ne h3]
        simp
    refine ⟨fun x => ⟨finGL E a (locGL E a w (cLoc w x)), key x⟩, ?_, fun x => ⟨?_, ?_⟩⟩
    · exact Continuous.subtype_mk (continuous_finGL_ad.comp ((CuspSub.continuous_locGL w).comp (continuous_cLoc w))) _
    · refine Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 (pInf_finGL _), Subgroup.mem_iInf.2 fun u =>
        Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 ?_⟩
      rw [cLoc_finGL]
      exact pLoc_locGL_of_ne (fun e => hu (by rw [e])) _
    · rw [cLoc_finGL]; exact pLoc_locGL _ _

theorem isClosed_finU : IsClosed ((finU E a : Subgroup (UA E a)) : Set (UA E a)) := by
  haveI : T2Space (GL (Fin a) (Cinf E)) := Units.isEmbedding_embedProduct.t2Space
  have hc : Continuous (cInf (E := E) (n := a)) :=
    (Continuous.units_map _ (continuous_id.matrix_map continuous_pInf_ad)).comp continuous_subtype_val
  exact isClosed_eq hc continuous_const

theorem t2GL (w : HeightOneSpectrum (𝓞 E)) : T2Space (GL (Fin a) (w.adicCompletion E)) :=
  Units.isEmbedding_embedProduct.t2Space

theorem isClosed_levelOf (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a))
    (hc : ∀ w, IsCompact (H w : Set (UA E a))) : IsClosed (levelOf a w₀ H : Set (UA E a)) := by
  have e : (levelOf a w₀ H : Set (UA E a)) = (finU E a : Set (UA E a)) ∩
      ((⋂ u, ⋂ (_ : ¬ Apart u w₀), {x | cLoc u x = 1}) ∩
        ⋂ w, ⋂ (_ : Apart w w₀), cLoc w ⁻¹' (cLoc w '' (H w : Set (UA E a)))) := by
    ext x
    simp only [SetLike.mem_coe, mem_levelOf, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_preimage,
      Set.mem_image]
  rw [e]
  refine isClosed_finU.inter (IsClosed.inter (isClosed_iInter fun u => isClosed_iInter fun _ => ?_)
    (isClosed_iInter fun w => isClosed_iInter fun _ => ?_))
  · haveI := t2GL (E := E) (a := a) u
    exact isClosed_eq (continuous_cLoc u) continuous_const
  · haveI := t2GL (E := E) (a := a) w
    exact ((hc w).image (continuous_cLoc w)).isClosed.preimage (continuous_cLoc w)

theorem exists_compact_of_finset (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)) (hle : ∀ w, H w ≤ locU a w)
    (hc : ∀ w, IsCompact (H w : Set (UA E a))) (R : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ C : Set (UA E a), IsCompact C ∧ ∀ x ∈ finU E a, (∀ u, (∀ r ∈ R, Apart u r) → cLoc u x ∈ GlobalTheory.LFun.KGL u a) →
      (∀ r ∈ R, ∃ y ∈ H r, cLoc r y = cLoc r x) → x ∈ C := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    obtain ⟨C, hC, hsub⟩ := exists_compact_integral (E := E) (a := a)
    exact ⟨C, hC, fun x hx hi _ => hsub x hx fun u => hi u (by simp)⟩
  | insert r R hr ih =>
    obtain ⟨C, hC, hsub⟩ := ih
    refine ⟨C * (H r : Set (UA E a)), hC.mul (hc r), fun x hx hi hH => ?_⟩
    obtain ⟨y, hy, hyx⟩ := hH r (Finset.mem_insert_self r R)
    by_cases hap : ∀ r' ∈ R, Apart r' r
    · have hyl := hle r hy
      have hy1 : ∀ u, Apart u r → cLoc u y = 1 := fun u hu => ((GlobalTheory.Cong.LevelExt.mem_locU_iff y).1 hyl).2 u hu
      have hyf : y ∈ finU E a := (Subgroup.mem_inf.1 hyl).1
      refine ⟨x * y⁻¹, hsub _ (mul_mem hx (inv_mem hyf)) ?_ ?_, y, hy, inv_mul_cancel_right x y⟩
      · intro u hu
        by_cases hur : Apart u r
        · rw [map_mul, map_inv, hy1 u hur, inv_one, mul_one]
          refine hi u fun r' hr' => ?_
          rcases Finset.mem_insert.1 hr' with rfl | h
          · exact hur
          · exact hu r' h
        · have hz : cLoc r (x * y⁻¹) ∈ GlobalTheory.LFun.KGL r a := by
            rw [map_mul, map_inv, hyx, mul_inv_cancel]; exact one_mem _
          rcases eq_or_eq_conjSrc (not_not.1 hur) with rfl | rfl
          · exact hz
          · exact integral_conjSrc _ r hz
      · intro r' h
        obtain ⟨y', hy', e'⟩ := hH r' (Finset.mem_insert_of_mem h)
        exact ⟨y', hy', by rw [map_mul, map_inv, hy1 r' (hap r' h), inv_one, mul_one]; exact e'⟩
    · push_neg at hap
      obtain ⟨r', hr', hnr⟩ := hap
      have hxC : x ∈ C := by
        refine hsub x hx (fun u hu => hi u fun r'' hr'' => ?_) (fun r'' h => hH r'' (Finset.mem_insert_of_mem h))
        rcases Finset.mem_insert.1 hr'' with rfl | h
        · intro hh
          exact not_apart_trans (not_not.2 hh) (not_apart_symm hnr) (hu r' hr')
        · exact hu r'' h
      exact ⟨x, hxC, 1, one_mem _, mul_one x⟩

theorem isLevelAway_levelOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, H w ≤ locU a w) → (∀ w u, ¬ Apart w u → H w = H u) → (∀ w, IsCompact (H w : Set (UA E a))) → (∀ w, IsOpen (((H w).subgroupOf (locU a w)) : Set (locU a w))) → (∀ᶠ w in Filter.cofinite, H w = GlobalTheory.Cong.AdaptLev.intU a w) → IsLevelAway w₀ (GlobalTheory.Cong.AdaptLev.levelOf a w₀ H) := by
  intro E _ _ _ a w₀ H hle _ hc ho hcof
  have hT := Filter.eventually_cofinite.1 hcof
  refine ⟨levelOf_le_finU w₀ H, fun x hx => (mem_levelOf.1 hx).2.1, ?_, ?_⟩
  · obtain ⟨C, hC, hsub⟩ := exists_compact_of_finset H hle hc hT.toFinset
    refine hC.of_isClosed_subset (isClosed_levelOf w₀ H hc) fun x hx => ?_
    obtain ⟨hf, h1, hw⟩ := mem_levelOf.1 hx
    refine hsub x hf (fun u hu => ?_) (fun r _ => ?_)
    · have hHu : H u = intU a u := by
        by_contra h
        exact hu u (hT.mem_toFinset.2 h) rfl
      by_cases h0 : Apart u w₀
      · obtain ⟨y, hy, e⟩ := hw u h0
        rw [hHu] at hy
        rw [← e]
        exact (mem_intU.1 hy).2 u (fun h => h rfl)
      · rw [h1 u h0]; exact one_mem _
    · by_cases h0 : Apart r w₀
      · exact hw r h0
      · exact ⟨1, one_mem _, by rw [map_one, h1 r h0]⟩
  · choose f hfc hf using fun w => exists_loc (E := E) (a := a) w
    let g : ∀ w, UA E a → locU a w := fun w x => ⟨f w x, (hf w x).1⟩
    have hg : ∀ w, Continuous (g w) := fun w => (hfc w).subtype_mk _
    have hpf : Continuous fun x : UA E a => GeneralLinearGroup.map (pFin E) (x : GA E a) :=
      (Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))).comp
        continuous_subtype_val
    refine ⟨{x | GeneralLinearGroup.map (pFin E) (x : GA E a) ∈ AdelicGLn.integralFiniteGL E a} ∩
      ⋂ w ∈ hT.toFinset, g w ⁻¹' ((H w).subgroupOf (locU a w) : Set (locU a w)), ?_, ?_, ?_⟩
    · exact ((AdelicGLn.isOpen_integralFiniteGL E a).preimage hpf).inter
        (isOpen_biInter_finset fun w _ => (ho w).preimage (hg w))
    · refine ⟨(integral_iff 1).2 fun u => by rw [map_one]; exact one_mem _, Set.mem_iInter₂.2 fun w _ => ?_⟩
      have h1 : f w 1 = 1 := eq_one_of_cLoc_eq_one (hf w 1).1 (by rw [(hf w 1).2, map_one])
      show (g w 1).1 ∈ H w
      show f w 1 ∈ H w
      rw [h1]; exact one_mem _
    · intro x hxN hxf hx1
      obtain ⟨hxi, hxH⟩ := hxN
      have hxi' := (integral_iff x).1 hxi
      refine mem_levelOf.2 ⟨hxf, hx1, fun w _ => ⟨f w x, ?_, (hf w x).2⟩⟩
      by_cases hwT : H w = intU a w
      · rw [hwT]; exact mem_intU_of (hf w x).1 (by rw [(hf w x).2]; exact hxi' w)
      · exact Set.mem_iInter₂.1 hxH w (hT.mem_toFinset.2 hwT)

end GlobalTheory.Cong.LevAway
