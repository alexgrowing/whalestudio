import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Development

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.PoincareInHH MeasureTheory

def KHg {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    Subgroup (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) :=
  (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).subgroupOf _

def unitaryLevelClosureSubgroup {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) :
    Subgroup (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) :=
  Subgroup.closure (Subtype.val ⁻¹' K2u X hb u)

def HaarRatio : Prop :=
  ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (K K' : Subgroup G), K' ≤ K → IsOpen (K' : Set G) →
    IsCompact (K : Set G) → (μ K).toReal / (μ K').toReal = (K'.relIndex K : ℝ)

def IdxGroupStep : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized →
    ((unitaryLevelClosureSubgroup X hb u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) =
      Subtype.val ⁻¹' K2u X hb u) ∧ unitaryLevelClosureSubgroup X hb u ≤ KHg X u

def IdxTopStep : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized →
    IsTopologicalGroup (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) ∧
      BorelSpace (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) ∧
      IsOpen (unitaryLevelClosureSubgroup X hb u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) ∧
      IsCompact (KHg X u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))

def IdxCountStep : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized →
    ((unitaryLevelClosureSubgroup X hb u).relIndex (KHg X u) : ℝ) = ∏ p : TypX X, ((glkC D.R.k (gOf p) : ℝ) / (ukC D.R.k (gOf p) : ℝ))

theorem colsIdxStep_of (hH : HaarRatio) (h1 : IdxGroupStep) (h2 : IdxTopStep) (h3 : IdxCountStep) :
    ColsIdxStep := by
  intro D X hb hK u hM hL
  obtain ⟨hG, hK2⟩ := h1 X hb hK u hM hL
  obtain ⟨hT, hB, hO, hC⟩ := h2 X hb hK u hM hL
  have hHaar : (X.measW u).μHf.IsHaarMeasure := (X.measW_norm u).2.2.1
  have hr := @hH _ _ _ hT _ hB (X.measW u).μHf hHaar (KHg X u) (unitaryLevelClosureSubgroup X hb u) hK2 hO hC
  rw [← h3 X hb hK u hM hL, ← hr, hG]
  rfl

end PIW.MassDataColumns
