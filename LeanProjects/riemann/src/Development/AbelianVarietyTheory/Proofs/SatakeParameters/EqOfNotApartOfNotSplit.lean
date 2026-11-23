import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenSubgroupCharacterKernel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorSplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Cong.AdaptLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def intU (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) : Subgroup (UA E a) :=
  locU a w ⊓ ⨅ (u : HeightOneSpectrum (𝓞 E)) (_ : ¬ Apart u w), (GlobalTheory.LFun.KGL u a).comap (cLoc u)

def iwaU (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) : Subgroup (UA E a) :=
  intU a w ⊓ (GlobalTheory.SmGL.iwahori (w.adicCompletion E) (Fin a)).comap (cLoc w)

def levelOf (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)) :
    Subgroup (UA E a) :=
  finU E a ⊓ (⨅ (u : HeightOneSpectrum (𝓞 E)) (_ : ¬ Apart u w₀), (cLoc u).ker) ⊓
    ⨅ (w : HeightOneSpectrum (𝓞 E)) (_ : Apart w w₀), ((H w).map (cLoc w)).comap (cLoc w)

variable {a : ℕ}

theorem mem_intU {w : HeightOneSpectrum (𝓞 E)} {x : UA E a} :
    x ∈ intU a w ↔ x ∈ locU a w ∧ ∀ u, ¬ Apart u w → cLoc u x ∈ GlobalTheory.LFun.KGL u a := by
  simp only [intU, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap]

theorem mem_levelOf {w₀ : HeightOneSpectrum (𝓞 E)} {H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)} {x : UA E a} :
    x ∈ levelOf a w₀ H ↔ x ∈ finU E a ∧ (∀ u, ¬ Apart u w₀ → cLoc u x = 1) ∧
      ∀ w, Apart w w₀ → ∃ y ∈ H w, cLoc w y = cLoc w x := by
  simp only [levelOf, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.mem_ker, Subgroup.mem_map, and_assoc]

theorem not_apart_symm {w u : HeightOneSpectrum (𝓞 E)} (h : ¬ Apart w u) : ¬ Apart u w := fun h' => h (Ne.symm h')

theorem not_apart_trans {w u v : HeightOneSpectrum (𝓞 E)} (h1 : ¬ Apart w u) (h2 : ¬ Apart u v) : ¬ Apart w v :=
  fun h => h ((not_not.1 h1).trans (not_not.1 h2))

theorem locU_congr {w u : HeightOneSpectrum (𝓞 E)} (h : ¬ Apart u w) : locU a u = locU a w := by
  have e : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) := not_not.1 h
  unfold locU
  rw [e]

theorem intU_congr {w u : HeightOneSpectrum (𝓞 E)} (h : ¬ Apart u w) : intU a u = intU a w := by
  ext x
  rw [mem_intU, mem_intU, locU_congr h]
  exact and_congr_right fun _ => forall_congr' fun v =>
    ⟨fun h' hv => h' (not_apart_trans hv (not_apart_symm h)), fun h' hv => h' (not_apart_trans hv h)⟩

theorem intU_le_locU (w : HeightOneSpectrum (𝓞 E)) : intU a w ≤ locU a w := inf_le_left

theorem levelOf_le_finU (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)) :
    levelOf a w₀ H ≤ finU E a := fun _ hx => (mem_levelOf.1 hx).1

theorem eq_of_not_apart_of_not_split {w u : HeightOneSpectrum (𝓞 E)} (hw : ¬ IsSplitAt w) (h : ¬ Apart u w) : u = w := by
  by_contra hne
  exact hw ⟨u, hne, not_not.1 h⟩

theorem cLoc_mem_KGL_of_not_apart {w u : HeightOneSpectrum (𝓞 E)} (h : ¬ Apart u w) (x : UA E a)
    (hx : cLoc w x ∈ GlobalTheory.LFun.KGL w a) : cLoc u x ∈ GlobalTheory.LFun.KGL u a := by
  rcases GlobalTheory.BCT.GlobLev.eq_or_eq_conjSrc (E := E) (not_not.1 h) with rfl | rfl
  · exact hx
  · exact GlobalTheory.BCT.GlobLev.integral_conjSrc x w hx

theorem mem_intU_of {w : HeightOneSpectrum (𝓞 E)} {x : UA E a} (hx : x ∈ locU a w) (hk : cLoc w x ∈ GlobalTheory.LFun.KGL w a) :
    x ∈ intU a w :=
  mem_intU.2 ⟨hx, fun _ hu => cLoc_mem_KGL_of_not_apart hu x hk⟩

theorem eq_one_of_cLoc_eq_one {w : HeightOneSpectrum (𝓞 E)} {x : UA E a} (hx : x ∈ locU a w) (h1 : cLoc w x = 1) :
    x = 1 := by
  by_cases hw : IsSplitAt w
  · exact congrArg Subtype.val (GlobalTheory.SplitPts.eq_one_of_cLoc hw ⟨x, hx⟩ h1)
  · have hall : ∀ u, cLoc u x = 1 := by
      intro u
      by_cases hu : Apart u w
      · exact ((GlobalTheory.Cong.LevelExt.mem_locU_iff x).1 hx).2 u hu
      · rw [eq_of_not_apart_of_not_split hw hu]; exact h1
    have hinf : cInf x = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hx).1
    refine Subtype.ext (ga_ext ?_ ?_)
    · exact hinf.trans (map_one _).symm
    · rw [Subgroup.coe_one, map_one]
      refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)
      have := congrArg (fun g : GL (Fin a) (u.adicCompletion E) => g.val i j) (hall u)
      simp only [Units.val_one, Matrix.one_apply] at this
      refine this.trans ?_
      split_ifs with hij <;> simp [hij]

theorem eq_of_cLoc_eq {w : HeightOneSpectrum (𝓞 E)} {x y : UA E a} (hx : x ∈ locU a w) (hy : y ∈ locU a w)
    (h : cLoc w x = cLoc w y) : x = y := by
  have := eq_one_of_cLoc_eq_one (mul_mem hx (inv_mem hy)) (by rw [map_mul, map_inv, h, mul_inv_cancel])
  exact mul_inv_eq_one.1 this

theorem coe_subgroupOf_image {G : Type} [Group G] {H L : Subgroup G} (h : H ≤ L) :
    Subtype.val '' ((H.subgroupOf L : Subgroup L) : Set L) = (H : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro hx; exact ⟨⟨x, h hx⟩, hx, rfl⟩

theorem isCompact_of_le {w : HeightOneSpectrum (𝓞 E)} {H : Subgroup (UA E a)} (hH : H ≤ intU a w)
    (ho : IsOpen ((H.subgroupOf (locU a w)) : Set (locU a w))) (hc : IsCompact (intU a w : Set (UA E a))) :
    IsCompact (H : Set (UA E a)) := by
  have hcl : IsClosed ((H.subgroupOf (locU a w)) : Set (locU a w)) := Subgroup.isClosed_of_isOpen _ ho
  have hc' : IsCompact (((intU a w).subgroupOf (locU a w)) : Set (locU a w)) := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff, coe_subgroupOf_image (intU_le_locU w)]
    exact hc
  have h2 := (hc'.of_isClosed_subset hcl fun x hx => hH hx).image continuous_subtype_val
  rwa [coe_subgroupOf_image (hH.trans (intU_le_locU w))] at h2

end GlobalTheory.Cong.AdaptLev
