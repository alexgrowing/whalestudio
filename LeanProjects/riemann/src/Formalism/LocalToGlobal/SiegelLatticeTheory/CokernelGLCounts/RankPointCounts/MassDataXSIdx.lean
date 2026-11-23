import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXTyped
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXHaarPos
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.UnipotentIntegralInLevel
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.EvalVOpen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.MemK2HpIffCong
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxCount
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxDone
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxCountStepOfModels
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.AdaptedBasisEveryPlace
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.LevelClauseAdaptedBasis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdaptRed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HModelAllOf

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets

namespace Formalism.L2.SG.Pf.MassDataX

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)

theorem comp_set_conjugated_level_eq : compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 =
    (fun z => PIW.MassDataColumns.xuP X hb u p * z * (PIW.MassDataColumns.xuP X hb u p)⁻¹) '' MassDataIdxSteps.KppX X hb p := by
  unfold MassDataIdxSteps.KppX compSet K2u
  rw [Set.image_image, Set.image_image]
  refine Set.image_congr fun y _ => ?_
  simp only [map_mul, map_inv]

theorem mem_compSet_iff (x : PIW.MassDataColumns.KvH X u p.1) :
    ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈
        compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 ↔
      x ∈ (PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1).subgroupOf (PIW.MassDataColumns.KvH X u p.1) := by
  rw [PIW.MassDataColumns.mem_K2Hp_iff X hb (Formalism.L2.SG.Closed.level_subgroup_is_group X) (Formalism.L2.SG.Closed.level_subgroup_properties X) u p x,
    comp_set_conjugated_level_eq]
  constructor
  · rintro ⟨z, hz, hzx⟩
    rw [← hzx]
    simpa [mul_assoc] using hz
  · intro h
    exact ⟨_, h, by group⟩

theorem idxHp_eq : MassDataLevelSSteps.idxHp X hb u p = PIW.MassDataColumns.lIdxH X hb u p := by
  have hKv : ∀ y : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u), (y : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 ↔ y ∈ PIW.MassDataColumns.KvH X u p.1 :=
    fun y => Iff.rfl
  have hC2 : Subgroup.closure (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) = PIW.MassDataColumns.KvH X u p.1 := by
    have e : (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) = (PIW.MassDataColumns.KvH X u p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) :=
      Set.ext hKv
    rw [e, Subgroup.closure_eq]
  have hS : ∀ y : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u), (y : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 →
      y ∈ PIW.MassDataColumns.KvH X u p.1 ∧ y ∈ PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1 := by
    intro y hy
    have hyK : y ∈ PIW.MassDataColumns.KvH X u p.1 :=
      (hKv y).1 ((level_compression_chain (X := X) (hb := hb) (p := p) u).2 hy)
    refine ⟨hyK, ?_⟩
    exact Subgroup.mem_subgroupOf.1 ((mem_compSet_iff X hb u p ⟨y, hyK⟩).1 hy)
  have hinf : Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) ⊓ PIW.MassDataColumns.KvH X u p.1 =
      PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1 ⊓ PIW.MassDataColumns.KvH X u p.1 := by
    have hle : Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) ≤ PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1 :=
      (Subgroup.closure_le _).2 fun y hy => (hS y hy).2
    refine le_antisymm (inf_le_inf_right _ hle) ?_
    rintro y ⟨hy2, hyK⟩
    refine ⟨Subgroup.subset_closure ?_, hyK⟩
    exact (mem_compSet_iff X hb u p ⟨y, hyK⟩).2 (Subgroup.mem_subgroupOf.2 hy2)
  have hsub : (Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)))).subgroupOf
      (PIW.MassDataColumns.KvH X u p.1) =
      (PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1).subgroupOf (PIW.MassDataColumns.KvH X u p.1) := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    have h1 := SetLike.ext_iff.1 hinf (x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))
    simp only [Subgroup.mem_inf] at h1
    exact ⟨fun h => (h1.1 ⟨h, x.2⟩).1, fun h => (h1.2 ⟨h, x.2⟩).1⟩
  unfold MassDataLevelSSteps.idxHp PIW.MassDataColumns.lIdxH
  rw [hC2]
  exact congrArg Subgroup.index hsub

theorem sTypIdx_holds : STypIdx := by
  intro D X hb u p hT _
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hL := Formalism.L2.SG.Closed.level_subgroup_properties X
  have h1 := MassDataLevelSSteps.haarIdxLoc_holds X hb hK hT hL u p
  rw [MassDataLevelSSteps.locLevi_holds X hb hK hT hL u p, idxHp_eq X hb u p] at h1
  obtain ⟨ρ, hs, hk, hc⟩ := (PIW.MassDataColumns.locRedH_of_rest (PIW.MassDataColumns.locRedRest_of_models
    (PIW.MassDataColumns.hModelAll_of (PIW.MassDataColumns.hAdaptAll_of PIW.MassDataColumns.adapted_basis_every_place)
      PIW.MassDataColumns.level_clause_adapted_basis))) X hb hK u hT hL p
  rw [PIW.MassDataColumns.lIdxH_eq_of_red X hb u p ρ hs hk hc] at h1
  exact h1

theorem typedAll_holds : Formalism.L2.SG.PoincareAmplitudeLowerBounds.TypedAll := typedAll_of_idx sTypIdx_holds

end Formalism.L2.SG.Pf.MassDataX
