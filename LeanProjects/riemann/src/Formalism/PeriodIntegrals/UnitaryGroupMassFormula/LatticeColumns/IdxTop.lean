import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.UnitaryLevelClosureSubgroup

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem isTopRing_tens : IsTopologicalRing (Af F ⊗[F] E) := by
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  first
  | exact IsModuleTopology.topologicalRing (Af F) (Af F ⊗[F] E)
  | exact IsModuleTopology.isTopologicalRing (Af F) (Af F ⊗[F] E)
  | exact IsModuleTopology.Module.isTopologicalRing (Af F) (Af F ⊗[F] E)
  | exact ModuleTopology.topologicalRing (Af F) (Af F ⊗[F] E)

private theorem subgroup_isTopologicalGroup {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (S : Subgroup G) : IsTopologicalGroup S :=
  inferInstance

theorem isTopGroup_HA : IsTopologicalGroup (HA (Af F) σ J) := by
  haveI := isTopRing_tens (F := F) (E := E)
  unfold HA HR Formalism.UG.UJ
  exact subgroup_isTopologicalGroup (G := GL (Fin n) (Af F ⊗[F] E)) _

theorem borel_HA : BorelSpace (HA (Af F) σ J) := ⟨rfl⟩

theorem sub_top_borel (H : Subgroup (HA (Af F) σ J)) : IsTopologicalGroup H ∧ BorelSpace H := by
  haveI := isTopGroup_HA σ J
  haveI := borel_HA σ J
  exact ⟨inferInstance, inferInstance⟩

end Gen

def OpenCompactStep : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized →
      IsOpen (unitaryLevelClosureSubgroup X hb u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) ∧
      IsCompact (KHg X u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))

theorem idxTopStep_of (h : OpenCompactStep) : IdxTopStep := by
  intro D X hb hK u hm hl
  obtain ⟨h1, h2⟩ := sub_top_borel X.B.I.cm.sig X.B.I.J (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))
  exact ⟨h1, h2, h X hb hK u hm hl⟩

end PIW.MassDataColumns
