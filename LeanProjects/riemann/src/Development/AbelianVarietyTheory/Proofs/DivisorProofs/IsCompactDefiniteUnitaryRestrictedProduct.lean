import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteUnitaryFinitePointsExistsOpenCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesCompactOfLocalBounds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedPlaceUnitaryLocalPointsEquivLocalUnitaryGro
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.LocCpt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

omit [IsCMField E] in
theorem continuous_mapLoc (w : Pl E) : Continuous (GeneralLinearGroup.map (n := Fin n) (pLoc E w)) :=
  Continuous.units_map _ (continuous_id.matrix_map (RestrictedProduct.continuous_eval w))

omit [IsCMField E] in
theorem entry_mem_of_mem_KGL {w : Pl E} {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GlobalTheory.LFun.KGL w n) (i j : Fin n) :
    g.val i j ∈ (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
  obtain ⟨k, rfl⟩ := hg
  exact (k.val i j).2

omit [IsCMField E] in

theorem isCompact_box (D : ∀ w : Pl E, Set (GL (Fin n) (w.adicCompletion E))) (hD : ∀ w, IsCompact (D w))
    (hDK : ∀ᶠ w in cofinite, D w ⊆ GlobalTheory.LFun.KGL w n) :
    IsCompact {g : GL (Fin n) (Af E) | ∀ w, GeneralLinearGroup.map (pLoc E w) g ∈ D w} := by
  let Q : Fin n → Fin n → ∀ w : Pl E, Set (w.adicCompletion E) := fun i j w =>
    (fun g : GL (Fin n) (w.adicCompletion E) => g.val i j) '' D w
  let Q' : Fin n → Fin n → ∀ w : Pl E, Set (w.adicCompletion E) := fun i j w =>
    (fun g : GL (Fin n) (w.adicCompletion E) => (g⁻¹).val i j) '' D w
  have hQ : ∀ i j w, IsCompact (Q i j w) := fun i j w =>
    (hD w).image (Units.continuous_val.matrix_elem i j)
  have hQ' : ∀ i j w, IsCompact (Q' i j w) := fun i j w =>
    (hD w).image (Units.continuous_coe_inv.matrix_elem i j)
  have hQK : ∀ i j, ∀ᶠ w in cofinite, Q i j w ⊆ (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    fun i j => hDK.mono fun w hw => by
      rintro _ ⟨g, hg, rfl⟩
      exact entry_mem_of_mem_KGL (hw hg) i j
  have hQK' : ∀ i j, ∀ᶠ w in cofinite, Q' i j w ⊆ (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    fun i j => hDK.mono fun w hw => by
      rintro _ ⟨g, hg, rfl⟩
      exact entry_mem_of_mem_KGL ((GlobalTheory.LFun.KGL w n).inv_mem (hw hg)) i j
  let P : Set (Matrix (Fin n) (Fin n) (Af E)) :=
    Set.univ.pi fun i => Set.univ.pi fun j => {a : Af E | ∀ w, a w ∈ Q i j w}
  let P' : Set (Matrix (Fin n) (Fin n) (Af E)) :=
    Set.univ.pi fun i => Set.univ.pi fun j => {a : Af E | ∀ w, a w ∈ Q' i j w}
  have hP : IsCompact P := isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
    GlobalTheory.IdeleCyl.isCompact_restrictedProduct_forall_mem (fun w : Pl E => w.adicCompletion E)
      (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) (Q i j) (hQ i j) (hQK i j)
  have hP' : IsCompact P' := isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
    GlobalTheory.IdeleCyl.isCompact_restrictedProduct_forall_mem (fun w : Pl E => w.adicCompletion E)
      (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) (Q' i j) (hQ' i j) (hQK' i j)
  have hC : IsClosed {g : GL (Fin n) (Af E) | ∀ w, GeneralLinearGroup.map (pLoc E w) g ∈ D w} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun w => ?_
    haveI : T2Space (GL (Fin n) (w.adicCompletion E)) := Units.isEmbedding_embedProduct.t2Space
    exact (hD w).isClosed.preimage (continuous_mapLoc w)
  refine IsCompact.of_isClosed_subset (Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hP.prod (hP'.image MulOpposite.continuous_op))) hC ?_
  intro g hg
  refine ⟨fun i _ j _ w => ⟨GeneralLinearGroup.map (pLoc E w) g, hg w, rfl⟩, ⟨(g⁻¹ : GL (Fin n) (Af E)).val, fun i _ j _ w => ?_, rfl⟩⟩
  refine ⟨GeneralLinearGroup.map (pLoc E w) g, hg w, ?_⟩
  show ((GeneralLinearGroup.map (pLoc E w) g)⁻¹ : GL (Fin n) (w.adicCompletion E)).val i j = _
  rw [← map_inv]
  rfl

end GlobalTheory.BCT.LocCpt

namespace GlobalTheory.BCT.LocCpt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_GLint_of_entries' {K : Type} [Field K] (O : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ a b, g.val a b ∈ O) (h2 : ∀ a b, (g⁻¹).val a b ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => by ext i j; exact congrFun (congrFun h i) j
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem mem_or_conj_mem {S : Set (Pl E)} (hS : IsSection S) (w : Pl E) :
    w ∈ S ∨ conjSrc (GlobalTheory.SplitPts.conjE E) w ∈ S := by
  obtain ⟨u, ⟨huS, hu⟩, -⟩ := hS w
  by_cases hw : IsSplitAt w
  · rcases (GlobalTheory.SplitPts.over_split hw).2.2 u hu with rfl | rfl
    · exact Or.inl huS
    · exact Or.inr huS
  · left
    by_contra hwS
    exact hw ⟨u, fun h => hwS (h ▸ huS), hu⟩

theorem cLoc_eq_invT (x : UA E n) (w : Pl E) :
    cLoc w x = invT n _ (GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) w)
      (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x)) := by
  set Y := GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) w) (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x)
  have h : (Y.val)ᵀ * (cLoc w x).val = 1 := GlobalTheory.SplitPts.comp_eq x w
  apply Units.ext
  show (cLoc w x).val = ((Y⁻¹).val)ᵀ
  calc (cLoc w x).val = ((Y⁻¹).val)ᵀ * ((Y.val)ᵀ * (cLoc w x).val) := by
        rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]
    _ = ((Y⁻¹).val)ᵀ := by rw [h, Matrix.mul_one]

end GlobalTheory.BCT.LocCpt

open GlobalTheory.BCT.LocCpt in

theorem GlobalTheory.BCT.LocCpt.loc_cpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ S : Set (Pl E),
    IsSection S → ∀ C : ∀ w : Pl E, Set (UL n w), (∀ w, IsCompact (C w)) → (∀ᶠ w in cofinite, C w = KL n w) →
    IsCompact {x : finU E n | ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) ∈ C w} := by
  intro E _ _ _ hU n S hS C hC hCK
  set c := GlobalTheory.SplitPts.conjE E
  let φ : ∀ w : Pl E, GL (Fin n) ((conjSrc c w).adicCompletion E) → GL (Fin n) (w.adicCompletion E) :=
    fun w g => invT n _ (GeneralLinearGroup.map (conjLoc c w) g)
  have hφ : ∀ w, Continuous (φ w) := fun w => (GlobalTheory.SplitPts.continuous_invT _).comp
    (Continuous.units_map _ (continuous_id.matrix_map (conjLoc_spec c w).1))
  let D : ∀ w : Pl E, Set (GL (Fin n) (w.adicCompletion E)) := fun w =>
    if w ∈ S then Subtype.val '' C w else φ w '' (Subtype.val '' C (conjSrc c w))
  have hD : ∀ w, IsCompact (D w) := by
    intro w
    by_cases hw : w ∈ S
    · simp only [D, if_pos hw]; exact (hC w).image continuous_subtype_val
    · simp only [D, if_neg hw]; exact ((hC _).image continuous_subtype_val).image (hφ w)
  have hDK : ∀ᶠ w in cofinite, D w ⊆ GlobalTheory.LFun.KGL w n := by
    have h1 : ∀ᶠ w in cofinite, C (conjSrc c w) = KL n (conjSrc c w) :=
      (conjSrc_injective c).tendsto_cofinite.eventually hCK
    filter_upwards [hCK, h1] with w hw hw'
    by_cases hwS : w ∈ S
    · simp only [D, if_pos hwS, hw]
      rintro _ ⟨k, hk, rfl⟩
      exact Subgroup.mem_subgroupOf.1 hk
    · simp only [D, if_neg hwS, hw']
      rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      have hk' : (k : GL (Fin n) _) ∈ GlobalTheory.LFun.KGL (conjSrc c w) n := Subgroup.mem_subgroupOf.1 hk
      have hO : ∀ y, y ∈ ((conjSrc c w).adicCompletionIntegers E : Set _) →
          conjLoc c w y ∈ (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := fun y hy => by
        rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, (conjLoc_spec c w).2.2 y]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hy
      apply mem_GLint_of_entries'
      · intro a b
        exact hO _ (entry_mem_of_mem_KGL ((GlobalTheory.LFun.KGL _ n).inv_mem hk') b a)
      · intro a b
        exact hO _ (entry_mem_of_mem_KGL hk' b a)
  have hB := isCompact_box D hD hDK

  have hmem : ∀ (x : finU E n) (w : Pl E), toSub (UL n w) (cLoc w (x : UA E n)) ∈ C w ↔
      cLoc w (x : UA E n) ∈ Subtype.val '' C w := by
    intro x w
    have hx := GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w (x : UA E n)
    rw [toSub, dif_pos hx]
    constructor
    · intro h; exact ⟨_, h, rfl⟩
    · rintro ⟨k, hk, e⟩
      have : k = ⟨_, hx⟩ := Subtype.ext e
      rwa [← this]
  have hclosed : IsClosed {x : finU E n | ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) ∈ C w} := by
    simp only [hmem, Set.setOf_forall]
    refine isClosed_iInter fun w => isClosed_iInter fun _ => ?_
    haveI : T2Space (GL (Fin n) (w.adicCompletion E)) := Units.isEmbedding_embedProduct.t2Space
    exact ((hC w).image continuous_subtype_val).isClosed.preimage
      ((GlobalTheory.DefU.Inert.continuous_cLoc w).comp continuous_subtype_val)

  haveI := GlobalTheory.DefU.LocAdm.t2Space_adelicGL_cmField (E := E) (n := n)
  have hfc : IsClosed ((finU E n : Subgroup (UA E n)) : Set (UA E n)) := by
    haveI : T2Space (GL (Fin n) (Cinf E)) := Units.isEmbedding_embedProduct.t2Space
    have hc := GlobalTheory.CuspRep.ContAut.continuous_map_pInf E n
    exact isClosed_eq (hc.comp continuous_subtype_val) continuous_const
  have hι : Topology.IsClosedEmbedding (fun x : finU E n => ((x : UA E n) : GA E n)) :=
    GlobalTheory.DefU.LocAdm.isClosed_UA.isClosedEmbedding_subtypeVal.comp hfc.isClosedEmbedding_subtypeVal
  refine IsCompact.of_isClosed_subset (hι.isCompact_preimage (hB.image GlobalTheory.DefU.LocAdm.continuous_finGL)) hclosed ?_
  intro x hx
  refine ⟨GeneralLinearGroup.map (pFin E) ((x : UA E n) : GA E n), fun w => ?_, ?_⟩
  · have e : ∀ u : Pl E, GeneralLinearGroup.map (pLoc E u) (GeneralLinearGroup.map (pFin E) ((x : UA E n) : GA E n)) =
        cLoc u (x : UA E n) := fun u => Units.ext rfl
    rw [e]
    by_cases hwS : w ∈ S
    · simp only [D, if_pos hwS]
      exact (hmem x w).1 (hx w hwS)
    · simp only [D, if_neg hwS]
      have hw' := (mem_or_conj_mem hS w).resolve_left hwS
      refine ⟨cLoc (conjSrc c w) (x : UA E n), (hmem x _).1 (hx _ hw'), ?_⟩
      exact (cLoc_eq_invT (x : UA E n) w).symm
  · have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E n) : GA E n) = 1 := x.2
    exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL])
