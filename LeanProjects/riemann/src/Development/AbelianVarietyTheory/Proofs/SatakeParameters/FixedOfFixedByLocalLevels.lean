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

namespace GlobalTheory.Cong.AdaptLevFix

open GlobalTheory.Cong.AdaptLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem eq_one_of_forall_cLoc {x : UA E a} (hx : x ∈ finU E a) (h : ∀ u, cLoc u x = 1) : x = 1 := by
  have hinf : cInf x = 1 := MonoidHom.mem_ker.1 hx
  refine Subtype.ext (ga_ext ?_ ?_)
  · exact hinf.trans (map_one _).symm
  · rw [Subgroup.coe_one, map_one]
    refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)
    have := congrArg (fun g : GL (Fin a) (u.adicCompletion E) => g.val i j) (h u)
    simp only [Units.val_one, Matrix.one_apply] at this
    refine this.trans ?_
    split_ifs with hij <;> simp [hij]

theorem isCompact_integral :
    IsCompact {k : finU E a | ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u a} := by
  have e' : ∀ k : finU E a, k ∈ (GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a).comap
      (GlobalTheory.BCT.GlobLev.finPart E a) ↔ ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u a := by
    intro k
    rw [Subgroup.mem_comap, GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
    simp only [GlobalTheory.BCT.GlobLev.mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles]
    exact ⟨fun h u => ⟨fun i j => h.1 i j u, fun i j => h.2 i j u⟩,
      fun h => ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩⟩
  have e : {k : finU E a | ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u a} =
      ((GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a).comap (GlobalTheory.BCT.GlobLev.finPart E a) :
        Set (finU E a)) := by
    ext k
    exact (e' k).symm
  have hO : IsOpen ((GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a).comap (GlobalTheory.BCT.GlobLev.finPart E a) :
      Set (finU E a)) :=
    (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E a).preimage GlobalTheory.BCT.GlobLev.continuous_finPart
  rw [e]
  refine IsCompact.of_isClosed_subset (GlobalTheory.BCT.GlobLev.isClosedEmbedding_finU.isCompact_preimage
      ((GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E a).image GlobalTheory.BCT.GlobLev.continuous_finGL_ad))
      (Subgroup.isClosed_of_isOpen _ hO) fun x hx => ⟨GlobalTheory.BCT.GlobLev.finPart E a x, hx, ?_⟩
  have h1 : Matrix.GeneralLinearGroup.map (pInf E) ((x : UA E a) : GA E a) = 1 := x.2
  exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

theorem exists_finite_fix {φ : UA E a → ℂ} (hφ : IsAutFormU φ) :
    ∃ t : Finset (HeightOneSpectrum (𝓞 E)), ∀ k ∈ finU E a, (∀ u, cLoc u k ∈ GlobalTheory.LFun.KGL u a) →
      (∀ u ∈ t, cLoc u k = 1) → RU E a k φ = φ := by
  haveI : ∀ u : HeightOneSpectrum (𝓞 E), T2Space (GL (Fin a) (u.adicCompletion E)) := fun u =>
    Units.isEmbedding_embedProduct.t2Space
  have hc := (isCompact_integral (E := E) (a := a)).diff hφ.level
  have hcov : {k : finU E a | ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u a} \ {k : finU E a | RU E a k φ = φ} ⊆
      ⋃ u, {k : finU E a | cLoc u k.1 ≠ 1} := by
    rintro k ⟨-, hk⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    by_contra hne
    push_neg at hne
    apply hk
    show RU E a k.1 φ = φ
    rw [eq_one_of_forall_cLoc k.2 hne, map_one]
    rfl
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover _ (fun u => isOpen_ne_fun
    ((GlobalTheory.BCT.GlobLev.continuous_cLoc u).comp continuous_subtype_val) continuous_const) hcov
  refine ⟨t, fun k hk hint h1 => ?_⟩
  by_contra hne
  have := ht (show (⟨k, hk⟩ : finU E a) ∈ _ from ⟨hint, hne⟩)
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at this
  obtain ⟨u, hu, hne'⟩ := this
  exact hne' (h1 u hu)

theorem one_of_cLoc_eq_one {q : HeightOneSpectrum (𝓞 E)} {z : UA E a} (h : cLoc q z = 1) :
    ∀ u, ¬ Apart u q → cLoc u z = 1 := by
  intro u hu
  by_cases hq : IsSplitAt q
  · exact GlobalTheory.Cong.LevelExt.one_of_cLoc hq z h u hu
  · rw [eq_of_not_apart_of_not_split hq hu]
    exact h

theorem peel (φ : UA E a → ℂ) (S : Set (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ k ∈ finU E a, (∀ u, cLoc u k ∈ GlobalTheory.LFun.KGL u a) → (∀ u ∈ S, cLoc u k = 1) → RU E a k φ = φ)
    (Q : Finset (HeightOneSpectrum (𝓞 E))) :
    ∀ x ∈ finU E a, (∀ u, (∀ q ∈ Q, Apart u q) → (u ∈ S → cLoc u x = 1) ∧ cLoc u x ∈ GlobalTheory.LFun.KGL u a) →
      (∀ q ∈ Q, ∃ y ∈ locU a q, RU E a y φ = φ ∧ cLoc q y = cLoc q x) → RU E a x φ = φ := by
  classical
  induction Q using Finset.induction_on with
  | empty =>
    intro x hx h1 _
    exact hS x hx (fun u => (h1 u (by simp)).2) (fun u hu => (h1 u (by simp)).1 hu)
  | @insert q Q hqQ ih =>
    intro x hx h1 h2
    obtain ⟨y, hyl, hyφ, hyq⟩ := h2 q (Finset.mem_insert_self q Q)
    have hyf : y ∈ finU E a := ((GlobalTheory.Cong.LevelExt.mem_locU_iff y).1 hyl).1
    have hya : ∀ u, Apart u q → cLoc u y = 1 := ((GlobalTheory.Cong.LevelExt.mem_locU_iff y).1 hyl).2
    have hq1 : cLoc q (y⁻¹ * x) = 1 := by rw [map_mul, map_inv, hyq, inv_mul_cancel]
    have hfib : ∀ u, ¬ Apart u q → cLoc u (y⁻¹ * x) = 1 := one_of_cLoc_eq_one hq1
    have happ : ∀ u, Apart u q → cLoc u (y⁻¹ * x) = cLoc u x := fun u hu => by
      rw [map_mul, map_inv, hya u hu, inv_one, one_mul]
    have key : RU E a (y⁻¹ * x) φ = φ := by
      refine ih (y⁻¹ * x) (mul_mem (inv_mem hyf) hx) (fun u hu => ?_) (fun q' hq' => ?_)
      · by_cases huq : Apart u q
        · rw [happ u huq]
          exact h1 u (fun p hp => by
            rcases Finset.mem_insert.1 hp with rfl | hp
            · exact huq
            · exact hu p hp)
        · rw [hfib u huq]
          exact ⟨fun _ => rfl, Subgroup.one_mem _⟩
      · by_cases hqq : Apart q' q
        · obtain ⟨y', hy'l, hy'φ, hy'q⟩ := h2 q' (Finset.mem_insert_of_mem hq')
          exact ⟨y', hy'l, hy'φ, hy'q.trans (happ q' hqq).symm⟩
        · exact ⟨1, Subgroup.one_mem _, by rw [map_one]; rfl, by rw [map_one, hfib q' hqq]⟩
    have hxe : x = y * (y⁻¹ * x) := by rw [mul_inv_cancel_left]
    rw [hxe, map_mul, Module.End.mul_apply, key, hyφ]

end GlobalTheory.Cong.AdaptLevFix

open GlobalTheory.Cong.AdaptLevFix in

theorem GlobalTheory.Cong.AdaptLev.fixed_of_levelOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, H w ≤ locU a w) → (∀ w u, ¬ Apart w u → H w = H u) → (∀ w, IsCompact (H w : Set (UA E a))) → (∀ w, IsOpen (((H w).subgroupOf (locU a w)) : Set (locU a w))) → (∀ᶠ w in Filter.cofinite, H w = GlobalTheory.Cong.AdaptLev.intU a w) → ∀ φ : UA E a → ℂ, IsAutFormU φ → (∀ w, Apart w w₀ → ∀ x ∈ H w, RU E a x φ = φ) → ∀ x ∈ GlobalTheory.Cong.AdaptLev.levelOf a w₀ H, RU E a x φ = φ := by
  intro E _ _ _ a w₀ H hHle _ _ _ hcof φ hφ hfix x hx
  classical
  obtain ⟨t, ht⟩ := exists_finite_fix hφ
  have hT : {w | ¬ H w = intU a w}.Finite := Filter.eventually_cofinite.1 hcof
  let Q : Finset (HeightOneSpectrum (𝓞 E)) := (t ∪ hT.toFinset).filter (fun w => Apart w w₀)
  obtain ⟨hxf, hx1, hxH⟩ := mem_levelOf.1 hx
  refine peel φ (t : Set _) (fun k hk hi h1 => ht k hk hi h1) Q x hxf (fun u hu => ?_) (fun q hq => ?_)
  · by_cases hu0 : Apart u w₀
    · have huQ : u ∉ Q := fun h => hu u h rfl
      have hut : u ∉ t := fun h => huQ (Finset.mem_filter.2 ⟨Finset.mem_union_left _ h, hu0⟩)
      have huT : H u = intU a u := by
        by_contra h
        exact huQ (Finset.mem_filter.2 ⟨Finset.mem_union_right _ (hT.mem_toFinset.2 h), hu0⟩)
      obtain ⟨y, hy, hyx⟩ := hxH u hu0
      rw [huT] at hy
      refine ⟨fun h => absurd h hut, ?_⟩
      rw [← hyx]
      exact (mem_intU.1 hy).2 u (fun h => h rfl)
    · rw [hx1 u hu0]
      exact ⟨fun _ => rfl, Subgroup.one_mem _⟩
  · have hq0 : Apart q w₀ := (Finset.mem_filter.1 hq).2
    obtain ⟨y, hy, hyx⟩ := hxH q hq0
    exact ⟨y, hHle q hy, hfix q hq0 y hy, hyx⟩
