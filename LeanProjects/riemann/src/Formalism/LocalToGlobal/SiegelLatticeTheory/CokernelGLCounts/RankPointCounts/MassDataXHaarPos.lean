import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataPos
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXRed
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXLeaves
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.UnitaryGroupSecondCountableT2
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LatStab
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepSize
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxTop

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets

namespace Formalism.L2.SG.Pf.MassDataX

theorem haar_toReal_pos {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] {U S K : Set G} (hU : IsOpen U) (hne : U.Nonempty) (h1 : U ⊆ S) (h2 : S ⊆ K)
    (hK : IsCompact K) : 0 < (μ S).toReal :=
  ENNReal.toReal_pos ((lt_of_lt_of_le (hU.measure_pos μ hne) (measure_mono h1)).ne')
    (ne_top_of_le_ne_top (hK.measure_lt_top (μ := μ)).ne (measure_mono h2))

theorem haar_toReal_pos' {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G)
    (hμ : μ.IsHaarMeasure) {U S K : Set G} (hU : IsOpen U) (hne : U.Nonempty) (h1 : U ⊆ S) (h2 : S ⊆ K)
    (hK : IsCompact K) : 0 < (μ S).toReal := by
  haveI := hμ
  exact haar_toReal_pos μ hU hne h1 h2 hK

section Typed

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (p : TypX X)

theorem kg_sub_kv : MassDataIdxSteps.KgX X p ⊆ MassDataIdxSteps.KvX X p := by
  intro x hx
  simp only [MassDataIdxSteps.KgX, MassDataIdxSteps.KvX] at hx ⊢
  exact hx.1

theorem kv_facts : IsOpen (MassDataIdxSteps.KvX X p) ∧ IsCompact (MassDataIdxSteps.KvX X p) ∧
    IsOpen (MassDataIdxSteps.KgX X p) ∧ (1 : MassDataIdxSteps.HAp X p) ∈ MassDataIdxSteps.KgX X p := by
  obtain ⟨K, hK, ho, hc, hg⟩ := stK_holds X p
  obtain ⟨ρ, -, hρ⟩ := stRed_holds X p K hK
  refine ⟨by rw [← hK]; exact ho, by rw [← hK]; exact hc, hg, ?_⟩
  have h1 := (hρ 1).mp (map_one ρ)
  simpa using h1

theorem kg_sub_kpp : MassDataIdxSteps.KgX X p ⊆ MassDataIdxSteps.KppX X hb p := by
  intro x hx
  obtain ⟨K, hK, -⟩ := stK_holds X p
  obtain ⟨ρ, hs, hρ⟩ := stRed_holds X p K hK
  obtain ⟨A, hA, hker, -⟩ := stImA_holds X hb p K hK ρ hs hρ
  have hxK : x ∈ (K : Set (MassDataIdxSteps.HAp X p)) := by
    rw [hK]
    exact kg_sub_kv X p hx
  rw [← hA]
  exact ⟨⟨x, hxK⟩, hker (MonoidHom.mem_ker.mpr ((hρ ⟨x, hxK⟩).mpr hx)), rfl⟩

theorem kpp_sub_kv : MassDataIdxSteps.KppX X hb p ⊆ MassDataIdxSteps.KvX X p := by
  obtain ⟨K, hK, -⟩ := stK_holds X p
  obtain ⟨ρ, hs, hρ⟩ := stRed_holds X p K hK
  obtain ⟨A, hA, -⟩ := stImA_holds X hb p K hK ρ hs hρ
  intro x hx
  rw [← hA] at hx
  obtain ⟨y, -, rfl⟩ := hx
  rw [← hK]
  exact y.2

theorem kg_sub_knat (u : D.what₂.Word) : MassDataIdxSteps.KgX X p ⊆ MassDataIdxSteps.KnatX X u p := by
  intro y hy
  have h1 : (1 : MassDataIdxSteps.HAp X p) ∈ MassDataIdxSteps.KvX X p := kg_sub_kv X p (kv_facts X p).2.2.2
  exact ⟨hy.1, 1, y, (Ssub _ _ _ _).one_mem, h1, hy, (one_mul y).symm⟩

theorem knat_sub_kv (u : D.what₂.Word) : MassDataIdxSteps.KnatX X u p ⊆ MassDataIdxSteps.KvX X p := fun _ h => h.1

end Typed

section Typed2

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (p : TypX X)

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures in

theorem level_compression_chain (u : D.what₂.Word) :
    MassDataIdxSteps.KgX X p ⊆ compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 ∧
      compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 ⊆ MassDataIdxSteps.KvX X p := by
  obtain ⟨K, hK, -, -, -⟩ := MassDataIdxSteps.stK_holds X p
  obtain ⟨ρ, -, hker⟩ := stRed_holds X p K hK
  have hKf := (PIW.MassDataColumns.finHA_mem_Kf_iff X hb (X.xu u)).2 (X.xu_K u)
  rw [Kf, Subgroup.mem_iInf] at hKf
  have haK : haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb (X.xu u)) ∈ MassDataIdxSteps.KvX X p := hKf p.1
  have hcs : compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 =
      (fun z => haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb (X.xu u)) * z *
        (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb (X.xu u)))⁻¹) ''
        MassDataIdxSteps.KppX X hb p := by
    unfold compSet K2u MassDataIdxSteps.KppX compSet
    rw [Set.image_image, Set.image_image]
    congr 1
    funext y
    rw [map_mul, map_mul, map_inv]
  rw [hcs]
  generalize haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb (X.xu u)) = a at haK ⊢
  have haK' : a ∈ (K : Set (MassDataIdxSteps.HAp X p)) := by rw [hK]; exact haK
  constructor
  · intro k hk
    have hkK : k ∈ (K : Set (MassDataIdxSteps.HAp X p)) := hK ▸ kg_sub_kv X p hk
    have h2 := (hker ((⟨a, haK'⟩ : K)⁻¹ * ⟨k, hkK⟩ * ⟨a, haK'⟩)).1
      (by rw [map_mul, map_mul, (hker ⟨k, hkK⟩).2 hk, mul_one, map_inv, inv_mul_cancel])
    have h2' : a⁻¹ * k * a ∈ MassDataIdxSteps.KgX X p := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h2
    refine ⟨a⁻¹ * k * a, kg_sub_kpp X hb p h2', ?_⟩
    group
  · rintro _ ⟨z, hz, rfl⟩
    have hzK : z ∈ (K : Set (MassDataIdxSteps.HAp X p)) := hK ▸ kpp_sub_kv X hb p hz
    rw [← hK]
    exact K.mul_mem (K.mul_mem haK' hzK) (K.inv_mem haK')

end Typed2

section Glob

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem conjugated_level_open_one_mem (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word) : IsOpen (K2u X hb u) ∧ (1 : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ K2u X hb u ∧
    K2u X hb u ⊆ (MassDataMassesW.KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have := PIW.MassDataColumns.isTopGroup_HA (F := X.B.I.F) (E := X.B.I.E) X.B.I.cm.sig X.B.I.J
  set e := Formalism.L2.SG.Pf.Meas.eFin X.B.I hb
  have h1 : IsOpen (levelUnitary X hb) := by
    have hk : levelUnitary X hb = e '' X.K2 := rfl
    rw [hk]
    exact e.toHomeomorph.isOpenMap _ (Formalism.L2.SG.Pf.level_subgroup_compact_open X).1
  set a := finHA X hb (X.xu u)
  have hc : K2u X hb u = ((Homeomorph.mulLeft a).trans (Homeomorph.mulRight a⁻¹)) '' levelUnitary X hb := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hc]
    exact ((Homeomorph.mulLeft a).trans (Homeomorph.mulRight a⁻¹)).isOpenMap _ h1
  · refine ⟨finHA X hb 1, ⟨1, hK.1, rfl⟩, ?_⟩
    show a * finHA X hb 1 * a⁻¹ = 1
    rw [finHA_eq_eFin, map_one, mul_one, mul_inv_cancel]
  · rintro _ ⟨y, ⟨k, hk2, rfl⟩, rfl⟩
    have hxu : a ∈ MassDataMassesW.KX X := (PIW.MassDataColumns.finHA_mem_Kf_iff X hb _).2 (X.xu_K u)
    have hkK : finHA X hb k ∈ MassDataMassesW.KX X :=
      (PIW.MassDataColumns.finHA_mem_Kf_iff X hb _).2 ((Formalism.L2.SG.Closed.level_subgroup_properties X).2.1 k hk2)
    exact (MassDataMassesW.KX X).mul_mem ((MassDataMassesW.KX X).mul_mem hxu hkK) ((MassDataMassesW.KX X).inv_mem hxu)

theorem closed_SNH_X (u : D.what₂.Word) :
    IsClosed (Ssub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) ∧
      IsClosed (Nsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) ∧
      IsClosed (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  exact PI.LevelKSplit.W.ExC.closed_SNH (MassDataVolumesW.stepHerm X) (fun x => star_star x) (frameOf X u) _
    (MassDataLevelSSteps.FrameW.frameOf_isStd X u)

end Glob

section Main

open Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.MassDataConc Formalism.L2.SG.Pf.MassDataPos

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem sv_pos (w : D.what₂.Word) (p : TypX X) {S : Set (MassDataIdxSteps.HAp X p)}
    (h1 : MassDataIdxSteps.KgX X p ⊆ S) (h2 : S ⊆ MassDataIdxSteps.KvX X p) :
    0 < ((X.measW w).μSv p.1 (Subtype.val ⁻¹' S)).toReal := by
  haveI := (X.measW_norm w).2.2.2.2.2.2.2.1 p.1
  obtain ⟨-, hc, hgo, h1g⟩ := kv_facts X p
  have hcl := MassDataLevelSSteps.LatTop.isClosed_Ssub (v := p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)
  exact haar_toReal_pos _ (hgo.preimage continuous_subtype_val)
    ⟨1, show (1 : MassDataIdxSteps.HAp X p) ∈ MassDataIdxSteps.KgX X p from h1g⟩
    (Set.preimage_mono h1) (Set.preimage_mono h2) (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hc)

theorem gv_pos (p : TypX X) {S : Set (MassDataIdxSteps.HAp X p)}
    (h1 : MassDataIdxSteps.KgX X p ⊆ S) (h2 : S ⊆ MassDataIdxSteps.KvX X p) :
    0 < (X.measG.μGv p.1 S).toReal := by
  haveI := X.measG_norm.2.2.2.1 p.1
  obtain ⟨-, hc, hgo, h1g⟩ := kv_facts X p
  exact haar_toReal_pos _ hgo ⟨1, h1g⟩ h1 h2 hc

theorem locHaarPosC_holds : LocHaarPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  have : FiniteDimensional X.B.I.F X.B.I.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have hKc := kCompactOpen_holds X
  have hKcs : ∀ w : D.what₂.Word, IsCompact (Subtype.val ⁻¹' (MassDataMassesW.KX X : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) :
      Set (Formalism.L2.SG.Sub.Ssub (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) := fun w =>
    (closed_SNH_X X w).1.isClosedEmbedding_subtypeVal.isCompact_preimage hKc.1
  have hKcn : ∀ w : D.what₂.Word, IsCompact (Subtype.val ⁻¹' (MassDataMassesW.KX X : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) :
      Set (Formalism.L2.SG.Sub.Nsub (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) := fun w =>
    (closed_SNH_X X w).2.1.isClosedEmbedding_subtypeVal.isCompact_preimage hKc.1
  have hKch : ∀ w : D.what₂.Word, IsCompact (Subtype.val ⁻¹' (MassDataMassesW.KX X : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) :
      Set (Formalism.L2.SG.Sub.Hsub (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) := fun w =>
    (closed_SNH_X X w).2.2.isClosedEmbedding_subtypeVal.isCompact_preimage hKc.1
  have h1K : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ (MassDataMassesW.KX X : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) :=
    (MassDataMassesW.KX X).one_mem
  refine ⟨fun p => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gv_pos X p (kg_sub_kv X p) subset_rfl
  · exact gv_pos X p (kg_sub_knat X p u) (knat_sub_kv X p u)
  · exact gv_pos X p (kg_sub_kpp X hb p) (kpp_sub_kv X hb p)
  · exact sv_pos X u p (kg_sub_kv X p) subset_rfl
  · exact sv_pos X u' p (kg_sub_kv X p) subset_rfl
  · exact sv_pos X u p (level_compression_chain X hb p u).1 (level_compression_chain X hb p u).2
  · exact sv_pos X u' p (level_compression_chain X hb p u').1 (level_compression_chain X hb p u').2
  · haveI := X.measG_norm.2.2.1
    exact haar_toReal_pos _ hKc.2 ⟨1, h1K⟩ subset_rfl subset_rfl hKc.1
  · haveI := (X.measW_norm u).2.2.2.2.2.2.1
    exact haar_toReal_pos _ (hKc.2.preimage continuous_subtype_val) ⟨1, h1K⟩ subset_rfl subset_rfl (hKcs u)
  · haveI := (X.measW_norm u').2.2.2.2.2.2.1
    exact haar_toReal_pos _ (hKc.2.preimage continuous_subtype_val) ⟨1, h1K⟩ subset_rfl subset_rfl (hKcs u')
  · exact haar_toReal_pos' _ (X.measW_norm u).2.2.1 (hKc.2.preimage continuous_subtype_val) ⟨1, h1K⟩ subset_rfl subset_rfl (hKch u)
  · exact haar_toReal_pos' _ (X.measW_norm u').2.2.1 (hKc.2.preimage continuous_subtype_val) ⟨1, h1K⟩ subset_rfl subset_rfl (hKch u')
  · obtain ⟨ho, h1, hs⟩ := conjugated_level_open_one_mem X hb hK u
    exact haar_toReal_pos' _ (X.measW_norm u).2.2.1 (ho.preimage continuous_subtype_val) ⟨1, h1⟩ subset_rfl (Set.preimage_mono hs) (hKch u)
  · obtain ⟨ho, h1, hs⟩ := conjugated_level_open_one_mem X hb hK u'
    exact haar_toReal_pos' _ (X.measW_norm u').2.2.1 (ho.preimage continuous_subtype_val) ⟨1, h1⟩ subset_rfl (Set.preimage_mono hs) (hKch u')
  · exact haar_toReal_pos' _ (X.measW_norm u).2.2.2.2.2.1 (hKc.2.preimage continuous_subtype_val) ⟨1, h1K⟩ subset_rfl subset_rfl (hKcn u)
  · exact haar_toReal_pos' _ (X.measW_norm u').2.2.2.2.2.1 (hKc.2.preimage continuous_subtype_val) ⟨1, h1K⟩ subset_rfl subset_rfl (hKcn u')

end Main

end Formalism.L2.SG.Pf.MassDataX
