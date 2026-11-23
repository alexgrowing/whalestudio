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

noncomputable section

namespace GlobalTheory.Cong.AutFormFix

open Matrix GlobalTheory.BCT.GlobLev GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem eq_one_of_forall_cLoc {x : UA E a} (hx : x ∈ finU E a) (h : ∀ u, cLoc u x = 1) : x = 1 := by
  refine Subtype.ext (ga_ext ?_ ?_)
  · exact (MonoidHom.mem_ker.1 hx).trans (map_one _).symm
  · rw [Subgroup.coe_one, map_one]
    refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)
    have := congrArg (fun g : GL (Fin a) (u.adicCompletion E) => g.val i j) (h u)
    simp only [Units.val_one, Matrix.one_apply] at this
    refine this.trans ?_
    split_ifs with hij <;> simp [hij]

theorem mem_integral_iff (k : finU E a) :
    k ∈ (AdelicGLn.integralFiniteGL E a).comap (finPart E a) ↔ ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u a := by
  rw [Subgroup.mem_comap, AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
  simp only [mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles]
  exact ⟨fun h u => ⟨fun i j => h.1 i j u, fun i j => h.2 i j u⟩,
    fun h => ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩⟩

theorem isCompact_integral :
    IsCompact (((AdelicGLn.integralFiniteGL E a).comap (finPart E a) : Subgroup (finU E a)) : Set (finU E a)) := by
  have hO : IsOpen (((AdelicGLn.integralFiniteGL E a).comap (finPart E a) : Subgroup (finU E a)) : Set (finU E a)) :=
    (AdelicGLn.isOpen_integralFiniteGL E a).preimage continuous_finPart
  refine IsCompact.of_isClosed_subset (isClosedEmbedding_finU.isCompact_preimage
    ((AdelicGLn.isCompact_integralFiniteGL E a).image continuous_finGL_ad))
    (Subgroup.isClosed_of_isOpen _ hO) fun x hx => ⟨finPart E a x, hx, ?_⟩
  have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E a) : GA E a) = 1 := x.2
  exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

end GlobalTheory.Cong.AutFormFix

namespace GlobalTheory.Cong.AutFormFix

open Matrix GlobalTheory.BCT.GlobLev GroundTheory.Automorphic

theorem fixed_intU_eventually : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (φ : UA E a → ℂ),
    IsAutFormU φ → ∀ᶠ w in Filter.cofinite, ∀ x ∈ GlobalTheory.Cong.AdaptLev.intU a w, RU E a x φ = φ := by
  intro E _ _ _ a φ hφ
  classical
  set St : Set (finU E a) := {k : finU E a | RU E a k φ = φ} with hSt
  set K₀ : Set (finU E a) := (((AdelicGLn.integralFiniteGL E a).comap (finPart E a) : Subgroup (finU E a)) : Set (finU E a))
  let t : Finset (HeightOneSpectrum (𝓞 E)) → Set (finU E a) := fun S =>
    {k : finU E a | ∀ u ∈ S, cLoc u k.1 = 1} ∩ Stᶜ
  have htc : ∀ S, IsClosed (t S) := by
    intro S
    refine IsClosed.inter ?_ hφ.level.isClosed_compl
    have : {k : finU E a | ∀ u ∈ S, cLoc u k.1 = 1} = ⋂ u ∈ S, {k : finU E a | cLoc u k.1 = 1} := by
      ext k; simp
    rw [this]
    refine isClosed_biInter fun u _ => ?_
    haveI : T2Space (GL (Fin a) (u.adicCompletion E)) := Units.isEmbedding_embedProduct.t2Space
    exact isClosed_eq ((continuous_cLoc u).comp continuous_subtype_val) continuous_const
  have hst : K₀ ∩ ⋂ S, t S = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun k hk => ?_
    have hall : ∀ u, cLoc u k.1 = 1 := fun u =>
      (Set.mem_iInter.1 hk.2 {u}).1 u (Finset.mem_singleton_self u)
    have h1 : k = 1 := Subtype.ext (eq_one_of_forall_cLoc k.2 hall)
    have hnot := (Set.mem_iInter.1 hk.2 ∅).2
    apply hnot
    rw [h1]
    show RU E a ((1 : finU E a) : UA E a) φ = φ
    rw [Subgroup.coe_one, map_one]; rfl
  have hdt : Directed (· ⊇ ·) t := by
    intro S₁ S₂
    refine ⟨S₁ ∪ S₂, ?_, ?_⟩ <;> rintro k ⟨hk, hk'⟩ <;> refine ⟨fun u hu => hk u ?_, hk'⟩ <;> simp [hu]
  obtain ⟨S, hS⟩ := isCompact_integral.elim_directed_family_closed t htc hst hdt
  have hfin : {w : HeightOneSpectrum (𝓞 E) | ¬ ∀ u ∈ S, Apart u w}.Finite := by
    refine ((S.finite_toSet.biUnion fun u _ => (Set.toFinite ({u, conjSrc (GlobalTheory.SplitPts.conjE E) u} : Set _)))).subset ?_
    intro w hw
    simp only [Set.mem_setOf_eq, not_forall, Apart, not_not] at hw
    obtain ⟨u, hu, he⟩ := hw
    refine Set.mem_biUnion hu ?_
    rcases eq_or_eq_conjSrc he.symm with rfl | rfl
    · simp
    · simp
  refine Filter.eventually_cofinite.2 (hfin.subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw ⊢
  intro hS'
  apply hw
  intro x hx
  obtain ⟨hxl, hxi⟩ := GlobalTheory.Cong.AdaptLev.mem_intU.1 hx
  have hxf : x ∈ finU E a := (Subgroup.mem_inf.1 hxl).1
  have hcomp : ∀ u, Apart u w → cLoc u x = 1 := fun u hu =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hxl).2 u) hu)
  have hK : (⟨x, hxf⟩ : finU E a) ∈ K₀ := by
    refine (mem_integral_iff _).2 fun u => ?_
    by_cases hu : Apart u w
    · show cLoc u x ∈ _
      rw [hcomp u hu]; exact one_mem _
    · exact hxi u hu
  by_contra hne
  have : (⟨x, hxf⟩ : finU E a) ∈ K₀ ∩ t S := ⟨hK, fun u hu => hcomp u (hS' u hu), hne⟩
  rw [hS] at this
  exact this

end GlobalTheory.Cong.AutFormFix
