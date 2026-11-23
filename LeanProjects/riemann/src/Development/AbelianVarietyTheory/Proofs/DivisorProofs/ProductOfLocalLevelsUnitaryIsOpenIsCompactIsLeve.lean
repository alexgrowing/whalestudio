import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import GroundTheory.AutomorphicForms.AdelicGLn

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.GlobLev

open GlobalTheory.SplitPts GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

omit [IsCMField E] in

theorem mem_KGL_iff_val (w : Pl E) (g : GLw n w) :
    g ∈ GlobalTheory.LFun.KGL w n ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1 := by
  have hO : GLnLocal.integralGL (w.adicCompletion E) n = GlobalTheory.LFun.KGL w n := by
    have h : (ValuativeRel.valuation (w.adicCompletion E)).integer = Formalism.UG.Ov E w :=
      Subring.ext fun x => GroundTheory.Global.mem_valuationInteger_iff w x
    rw [GlobalTheory.LFun.KGL, ← h]; rfl
  rw [← hO, GLnLocal.mem_integralGL_iff]
  simp only [GroundTheory.Global.mem_valuationInteger_iff]
  rfl

theorem eq_or_eq_conjSrc {w u : Pl E}
    (h : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) :
    u = w ∨ u = conjSrc (conjE E) w := by
  by_cases huw : u = w
  · exact Or.inl huw
  · exact (over_split ⟨u, huw, h⟩).2.2 u h

theorem conjSrc_eq_of_not_split {w : Pl E} (hw : ¬ IsSplitAt w) : conjSrc (conjE E) w = w := by
  by_contra hne
  exact hw ⟨_, hne, (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w _).2
      (Or.inr (conjPl_self_conjSrc w))⟩

theorem conjLoc_eq_cj {w : Pl E} (hw : ¬ IsSplitAt w) (a : Af E) :
    conjLoc (conjE E) w (pLoc E (conjSrc (conjE E) w) a) = cj w (pLoc E w a) := by
  have key : ∀ (v : Pl E) (_ : v = w) (f : v.adicCompletion E →+* w.adicCompletion E), Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (conjE E k)) → f (pLoc E v a) = cj w (pLoc E w a) := by
    rintro v rfl f hf h
    have hex : ∃ s : v.adicCompletion E →+* v.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := ⟨f, hf, h⟩
    rw [cj, dif_pos hex]
    exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf hex.choose_spec.1
      (funext fun k => (h k).trans (hex.choose_spec.2 k).symm)) _
  exact key _ (conjSrc_eq_of_not_split hw) _ (conjLoc_spec (conjE E) _).1 (conjLoc_spec (conjE E) _).2.1

theorem cLoc_mem_UL (w : Pl E) (x : UA E n) : cLoc w x ∈ UL n w := by
  unfold UL
  split_ifs with hw
  · exact Subgroup.mem_top _
  · have h := comp_eq x w
    have e : (cLoc (conjSrc (conjE E) w) x).val.map (conjLoc (conjE E) w) = (cLoc w x).val.map (cj w) :=
      Matrix.ext fun i j => conjLoc_eq_cj hw _
    rw [e] at h
    change ((cLoc w x).val.map (cj w))ᵀ * 1 * (cLoc w x).val = 1
    rw [Matrix.mul_one]
    exact h

theorem val_inv_entry (x : UA E n) (u : Pl E) (i j : Fin n) :
    Valued.v (((cLoc u x)⁻¹).val i j) = Valued.v ((cLoc (conjSrc (conjE E) u) x).val j i) := by
  have h := comp_eq x u
  have e : ((cLoc u x)⁻¹).val = ((cLoc (conjSrc (conjE E) u) x).val.map (conjLoc (conjE E) u))ᵀ :=
    (Units.eq_inv_of_mul_eq_one_right h).symm
  rw [e]
  exact (conjLoc_spec (conjE E) u).2.2 _

theorem integral_conjSrc (x : UA E n) (u : Pl E) (h : cLoc u x ∈ GlobalTheory.LFun.KGL u n) :
    cLoc (conjSrc (conjE E) u) x ∈ GlobalTheory.LFun.KGL (conjSrc (conjE E) u) n := by
  rw [mem_KGL_iff_val] at h ⊢
  refine ⟨fun i j => (val_inv_entry x u j i) ▸ h.2 j i, fun i j => ?_⟩
  have h2 := val_inv_entry x⁻¹ u j i
  rw [map_inv, map_inv, inv_inv] at h2
  exact h2 ▸ h.1 j i

theorem mem_globLev (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (k : finU E n) :
    k ∈ globLev S K' ↔ ∀ w ∈ S, (⟨cLoc w k.1, cLoc_mem_UL w k.1⟩ : UL n w) ∈ K' w := by
  simp only [globLev, Subgroup.mem_iInf, Subgroup.mem_comap]
  refine forall₂_congr fun w _ => ⟨?_, fun h => ⟨_, h, rfl⟩⟩
  rintro ⟨a, ha, e⟩
  have : a = ⟨cLoc w k.1, cLoc_mem_UL w k.1⟩ := Subtype.ext e
  exact this ▸ ha

variable (E n) in

def finPart : finU E n →* GL (Fin n) (Af E) :=
  (GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (finU E n).subtype)

theorem continuous_finPart : Continuous (finPart E n) :=
  (Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))).comp
    (continuous_subtype_val.comp continuous_subtype_val)

theorem globLev_KL_eq {S : Set (Pl E)} (hS : IsSection S) :
    globLev S (KL n) = (AdelicGLn.integralFiniteGL E n).comap (finPart E n) := by
  ext k
  have e : k ∈ (AdelicGLn.integralFiniteGL E n).comap (finPart E n) ↔ ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u n := by
    rw [Subgroup.mem_comap, AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
    simp only [mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles]
    exact ⟨fun h u => ⟨fun i j => h.1 i j u, fun i j => h.2 i j u⟩,
      fun h => ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩⟩
  rw [e, mem_globLev]
  refine ⟨fun h u => ?_, fun h w _ => h w⟩
  obtain ⟨w, ⟨hw, hwu⟩, -⟩ := hS u
  rcases eq_or_eq_conjSrc hwu.symm with rfl | rfl
  · exact h u hw
  · exact integral_conjSrc k.1 w (h w hw)

theorem continuous_pInf_ad : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_conj_ad : Continuous (conjAd E) :=
  ((continuous_infEq E).comp (continuous_star.comp continuous_pInf_ad)).prodMk
    ((continuous_conjFin _).comp continuous_snd)

theorem isClosedEmbedding_finU : Topology.IsClosedEmbedding (fun x : finU E n => ((x : UA E n) : GA E n)) := by
  haveI : T2Space (FiniteAdeleRing (𝓞 E) E) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))
  haveI : T2Space (InfiniteAdeleRing E) := inferInstanceAs (T2Space ((v : InfinitePlace E) → v.Completion))
  haveI : T2Space (Ad E) := inferInstanceAs (T2Space (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E))
  have h1 : IsClosed ((UA E n : Subgroup (GA E n)) : Set (GA E n)) := by
    show IsClosed {g : GA E n | ((g : Matrix (Fin n) (Fin n) (Ad E)).map (conjAd E))ᵀ * 1 *
      (g : Matrix (Fin n) (Fin n) (Ad E)) = 1}
    exact isClosed_eq (((Units.continuous_val.matrix_map continuous_conj_ad).matrix_transpose.matrix_mul
      continuous_const).matrix_mul Units.continuous_val) continuous_const
  have h2 : IsClosed ((finU E n : Subgroup (UA E n)) : Set (UA E n)) := by
    haveI : T2Space (GL (Fin n) (Cinf E)) := Units.isEmbedding_embedProduct.t2Space
    have hc : Continuous (cInf (E := E) (n := n)) :=
      (Continuous.units_map _ (continuous_id.matrix_map continuous_pInf_ad)).comp continuous_subtype_val
    exact isClosed_eq hc continuous_const
  exact h1.isClosedEmbedding_subtypeVal.comp h2.isClosedEmbedding_subtypeVal

theorem continuous_finGL_ad : Continuous (finGL E n) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))

theorem continuous_cLoc (w : Pl E) : Continuous (cLoc (n := n) w) :=
  (Continuous.units_map _ (continuous_id.matrix_map
    ((RestrictedProduct.continuous_eval w).comp continuous_snd))).comp continuous_subtype_val

theorem globLev_isOpen_isCompact_isLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' →
    IsOpen (globLev S (KL n) : Set (finU E n)) ∧ IsCompact (globLev S (KL n) : Set (finU E n)) ∧
      IsLevel (MonoidHom.id _) (globLev S (KL n)) (globLev S K') := by
  intro E _ _ _ _ n _ S hS K' hK
  have hO : IsOpen (globLev S (KL n) : Set (finU E n)) := by
    rw [globLev_KL_eq hS]
    exact (AdelicGLn.isOpen_integralFiniteGL E n).preimage continuous_finPart
  have hle : globLev S K' ≤ globLev S (KL n) := fun k hk =>
    (mem_globLev S _ k).2 fun w hw => (hK.1 w).2.1 ((mem_globLev S _ k).1 hk w hw)
  refine ⟨hO, ?_, ?_, hle, fun k hk => hk⟩
  · refine IsCompact.of_isClosed_subset (isClosedEmbedding_finU.isCompact_preimage
      ((AdelicGLn.isCompact_integralFiniteGL E n).image continuous_finGL_ad))
      (Subgroup.isClosed_of_isOpen _ hO) fun x hx => ⟨finPart E n x, ?_, ?_⟩
    · rw [globLev_KL_eq hS] at hx
      exact hx
    · have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E n) : GA E n) = 1 := x.2
      exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)
  · have hfin : {w | w ∈ S ∧ K' w ≠ KL n w}.Finite := (Filter.eventually_cofinite.1 hK.2).subset fun w hw => hw.2
    have e : (globLev S K' : Set (finU E n)) = (globLev S (KL n) : Set (finU E n)) ∩
        ⋂ w ∈ {w | w ∈ S ∧ K' w ≠ KL n w},
          (fun k : finU E n => (⟨cLoc w k.1, cLoc_mem_UL w k.1⟩ : UL n w)) ⁻¹' (K' w : Set (UL n w)) := by
      ext k
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
      refine ⟨fun hk => ⟨hle hk, fun w hw => (mem_globLev S _ k).1 hk w hw.1⟩, fun hk => ?_⟩
      refine (mem_globLev S _ k).2 fun w hw => ?_
      by_cases h : K' w = KL n w
      · rw [h]; exact (mem_globLev S _ k).1 hk.1 w hw
      · exact hk.2 w ⟨hw, h⟩
    rw [e]
    exact hO.inter (hfin.isOpen_biInter fun w _ => (hK.1 w).1.preimage
      (Continuous.subtype_mk ((continuous_cLoc w).comp continuous_subtype_val) _))

end GlobalTheory.BCT.GlobLev
