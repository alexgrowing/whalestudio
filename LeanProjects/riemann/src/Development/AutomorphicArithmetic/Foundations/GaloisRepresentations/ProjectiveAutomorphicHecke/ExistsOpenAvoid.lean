import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantPositivePeterssonForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocEqOneOfMemGam
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap.PNbhd2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem exists_open_avoid (w : Plc E) (x : GLw n w) (hx : x ≠ 1) :
    ∃ V : Subgroup (GLw n w), IsOpen (V : Set (GLw n w)) ∧ V ≤ GlobalTheory.LFun.KGL w n ∧ x ∉ V := by
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  by_cases hxK : x ∈ GlobalTheory.LFun.KGL w n
  swap
  · exact ⟨_, hKo, le_rfl, hxK⟩
  have hne : ∃ i j, x.val i j ≠ (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j := by
    by_contra h
    push_neg at h
    exact hx (Units.ext (Matrix.ext h))
  obtain ⟨i, j, hij⟩ := hne
  haveI : CompactSpace ↥(GlobalTheory.LFun.KGL w n) := isCompact_iff_compactSpace.1 hKc
  let f : ↥(GlobalTheory.LFun.KGL w n) → w.adicCompletion E :=
    fun g => g.1.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j
  have hf : Continuous f :=
    Continuous.sub (Continuous.matrix_elem (Units.continuous_val.comp continuous_subtype_val) i j) continuous_const
  obtain ⟨A, hA⟩ := NonarchimedeanAddGroup.is_nonarchimedean
    ({x.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j}ᶜ : Set (w.adicCompletion E))
    (isOpen_compl_singleton.mem_nhds (by simpa using (sub_ne_zero.2 hij).symm))
  have hW : IsClopen (f ⁻¹' (A : Set (w.adicCompletion E))) := A.isClopen.preimage hf
  have h1 : (1 : ↥(GlobalTheory.LFun.KGL w n)) ∈ f ⁻¹' (A : Set (w.adicCompletion E)) := by
    simp [f, A.zero_mem]
  obtain ⟨H, hH⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hW h1
  refine ⟨(H : Subgroup _).map (GlobalTheory.LFun.KGL w n).subtype, ?_, Subgroup.map_subtype_le _, ?_⟩
  · exact hKo.isOpenEmbedding_subtypeVal.isOpenMap _ H.isOpen
  · rintro ⟨h, hh, rfl⟩
    exact hA (hH hh) rfl

private theorem exists_Kw
    (F : Finset (Σ w : Plc E, {V : Subgroup (GLw n w) // IsOpen (V : Set (GLw n w)) ∧ V ≤ GlobalTheory.LFun.KGL w n})) :
    ∃ Kw : ∀ w : Plc E, Subgroup (GLw n w), (∀ w, IsOpen (Kw w : Set (GLw n w)) ∧ Kw w ≤ GlobalTheory.LFun.KGL w n) ∧
      ∀ i ∈ F, Kw i.1 ≤ i.2.1 := by
  induction F using Finset.induction_on with
  | empty =>
    exact ⟨fun w => GlobalTheory.LFun.KGL w n,
      fun w => ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).1, le_rfl⟩, by simp⟩
  | insert i F _ ih =>
    obtain ⟨Kw, h1, h2⟩ := ih
    obtain ⟨v, V, hVo, hVK⟩ := i
    have hle : ∀ w, Function.update Kw v (Kw v ⊓ V) w ≤ Kw w := fun w => by
      by_cases h : w = v
      · subst h
        rw [Function.update_self]
        exact inf_le_left
      · rw [Function.update_of_ne h]
    refine ⟨Function.update Kw v (Kw v ⊓ V), fun w => ?_, fun j hj => ?_⟩
    · refine ⟨?_, (hle w).trans (h1 w).2⟩
      by_cases h : w = v
      · subst h
        rw [Function.update_self]
        exact (h1 w).1.inter hVo
      · rw [Function.update_of_ne h]
        exact (h1 w).1
    · rcases Finset.mem_insert.1 hj with rfl | hj
      · simp only [Function.update_self]
        exact inf_le_right
      · exact (hle j.1).trans (h2 j hj)

end UpperTheory.Gal.CertificateRingHomMap.PNbhd2

theorem UpperTheory.Gal.CertificateRingHomMap.pNbhd2_of :
    UpperTheory.Gal.CertificateRingHomMap.Nbhd2 := by
  intro E _ _ _ n O hO
  haveI := GlobalTheory.DefU.LocAdm.t2Space_adelicGL_cmField (E := E) (n := n)
  let p : finU E n →* GL (Fin n) (Af E) :=
    (GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (finU E n).subtype)
  have hp : Continuous p := continuous_map_pFin.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hfin : ∀ x : UA E n, x ∈ finU E n ↔
      finGL E n (GeneralLinearGroup.map (pFin E) (x : GA E n)) = (x : GA E n) := by
    intro x
    constructor
    · intro hx
      have h1 : GeneralLinearGroup.map (pInf E) (x : GA E n) = 1 := hx
      exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL])
    · intro hx
      change GeneralLinearGroup.map (pInf E) (x : GA E n) = 1
      rw [← hx, pInf_finGL]
  have hc : IsClosed ((finU E n : Subgroup (UA E n)) : Set (UA E n)) := by
    have e : ((finU E n : Subgroup (UA E n)) : Set (UA E n)) =
        {x : UA E n | finGL E n (GeneralLinearGroup.map (pFin E) (x : GA E n)) = (x : GA E n)} :=
      Set.ext hfin
    rw [e]
    exact isClosed_eq (GlobalTheory.DefU.LocAdm.continuous_finGL.comp (continuous_map_pFin.comp continuous_subtype_val))
      continuous_subtype_val
  have hι : Topology.IsClosedEmbedding (fun x : finU E n => ((x : UA E n) : GA E n)) :=
    GlobalTheory.DefU.LocAdm.isClosed_UA.isClosedEmbedding_subtypeVal.comp hc.isClosedEmbedding_subtypeVal
  have hKc := GlobalTheory.EulerTwRestr.isCompact_Kglob (E := E) (n := n)
  have hKo := GlobalTheory.EulerTwRestr.isOpen_Kglob (E := E) (n := n)
  have hC : IsCompact {u : finU E n | p u ∈ GlobalTheory.EulerTw.Kglob E n} :=
    IsCompact.of_isClosed_subset (hι.isCompact_preimage (hKc.image GlobalTheory.DefU.LocAdm.continuous_finGL))
      ((Subgroup.isClosed_of_isOpen _ hKo).preimage hp) fun x hx => ⟨p x, hx, (hfin x).1 x.2⟩
  have hL : ∀ w : Plc E, Continuous fun u : finU E n => cLoc w u.1 := fun w =>
    (show Continuous (GeneralLinearGroup.map (n := Fin n) (pLoc E w)) from
      Continuous.units_map _ (Continuous.matrix_map continuous_id
        (show Continuous (pLoc E w) from RestrictedProduct.continuous_eval
          (R := fun w : Plc E => w.adicCompletion E)
          (A := fun w : Plc E => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) w))).comp hp
  let D : (Σ w : Plc E, {V : Subgroup (GLw n w) // IsOpen (V : Set (GLw n w)) ∧ V ≤ GlobalTheory.LFun.KGL w n}) →
      Set (finU E n) := fun i => {u | cLoc i.1 u.1 ∈ i.2.1}
  have hD : ∀ i, IsClosed (D i) := fun i => (Subgroup.isClosed_of_isOpen _ i.2.2.1).preimage (hL i.1)
  have hone : ∀ u : finU E n, (∀ i, u ∈ D i) → u = 1 := by
    intro u hu
    have h1 : ∀ w : Plc E, cLoc w u.1 = 1 := by
      intro w
      by_contra hne
      obtain ⟨V, hVo, hVK, hV⟩ := UpperTheory.Gal.CertificateRingHomMap.PNbhd2.exists_open_avoid w _ hne
      exact hV (hu ⟨w, V, hVo, hVK⟩)
    have h2 : p u = 1 := GlobalTheory.EulerTwRestr.gl_ext fun w => (h1 w).trans (map_one _).symm
    have h3 : GeneralLinearGroup.map (pInf E) (u.1 : GA E n) = 1 := u.2
    exact Subtype.ext (Subtype.ext (ga_ext (by rw [h3]; simp) (by simpa using (show GeneralLinearGroup.map (pFin E) (u.1 : GA E n) = 1 from h2))))
  have hemp : ({u : finU E n | p u ∈ GlobalTheory.EulerTw.Kglob E n} \ (O : Set (finU E n))) ∩ ⋂ i, D i = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun u hu => ?_
    have := hone u (Set.mem_iInter.1 hu.2)
    exact hu.1.2 (this ▸ O.one_mem)
  obtain ⟨F, hF⟩ := (hC.diff hO).elim_finite_subfamily_closed D hD hemp
  obtain ⟨Kw, hK1, hK2⟩ := UpperTheory.Gal.CertificateRingHomMap.PNbhd2.exists_Kw F
  refine ⟨F.image Sigma.fst, Kw, hK1, fun u hu hS => ?_⟩
  by_contra huO
  have hmem : u ∈ ({u : finU E n | p u ∈ GlobalTheory.EulerTw.Kglob E n} \ (O : Set (finU E n))) ∩ ⋂ i ∈ F, D i :=
    ⟨⟨GlobalTheory.EulerTwRestr.mem_Kglob.2 hu, huO⟩,
      Set.mem_iInter₂.2 fun i hi => hK2 i hi (hS i.1 (Finset.mem_image_of_mem _ hi))⟩
  rw [hF] at hmem
  exact hmem
