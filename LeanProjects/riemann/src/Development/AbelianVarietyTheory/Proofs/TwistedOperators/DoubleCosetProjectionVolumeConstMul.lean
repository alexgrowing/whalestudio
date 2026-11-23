import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowGrpEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Definitions.Divisors.GridTestLatticeLargestSlopeBound
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorAtSplitPlaceIsoty
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VolumePeriodProjectionSetEqFamilyLevelStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

noncomputable section

namespace GlobalTheory.CellLevel

variable {D : D7}

theorem finE_range_eq (V : HSp D) : ((Lev.finE V).comp (GfC V).subtype).range = (Lev.finE V).range := by
  refine le_antisymm (fun y ⟨g, hg⟩ => ⟨g.1, hg⟩) ?_
  rintro _ ⟨g, rfl⟩
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 _ (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V g)
  refine ⟨⟨k, MonoidHom.mem_ker.2 k1⟩, ?_⟩
  show Formalism.UG.bc (Lev.swapAE D) (finHom V k) = Formalism.UG.bc (Lev.swapAE D) (finHom V g)
  rw [k2]

theorem relIndex_comap_fin (V : HSp D) (K K' : Subgroup (GL (Fin V.rank) (Lev.EAf D))) :
    (K.comap ((Lev.finE V).comp (GfC V).subtype)).relIndex (K'.comap ((Lev.finE V).comp (GfC V).subtype)) =
      (K.comap (Lev.finE V)).relIndex (K'.comap (Lev.finE V)) := by
  rw [Subgroup.relIndex_comap, Subgroup.relIndex_comap, Subgroup.map_comap_eq, Subgroup.map_comap_eq,
    finE_range_eq]

theorem isCompact_comap_fin (V : HSp D) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))} (h : IsCO V K) :
    IsCompact ((K.comap ((Lev.finE V).comp (GfC V).subtype) : Subgroup (GfC V)) : Set (GfC V)) := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  convert h.2 using 1
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact Lev.mem_levA.2 ⟨g.2, hg⟩
  · intro hy
    obtain ⟨h1, h2⟩ := Lev.mem_levA.1 hy
    exact ⟨⟨y, h1⟩, h2, rfl⟩

theorem isOpen_comap_fin (V : HSp D) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))}
    (h : IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V))) :
    IsOpen ((K.comap ((Lev.finE V).comp (GfC V).subtype) : Subgroup (GfC V)) : Set (GfC V)) :=
  h.preimage continuous_subtype_val

theorem relIndex_ne_zero (V : HSp D) {K K₃ : Subgroup (GL (Fin V.rank) (Lev.EAf D))} (h : IsCO V K)
    (h₃ : IsOpen ((K₃.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V))) :
    (K₃.comap ((Lev.finE V).comp (GfC V).subtype)).relIndex (K.comap ((Lev.finE V).comp (GfC V).subtype)) ≠ 0 := by
  have := GlobalTheory.LocVec.finiteIndex_of_isOpen (K.comap ((Lev.finE V).comp (GfC V).subtype)) (isCompact_comap_fin V h) subset_rfl
    ((K₃.comap ((Lev.finE V).comp (GfC V).subtype)).subgroupOf (K.comap ((Lev.finE V).comp (GfC V).subtype)))
    ((isOpen_comap_fin V h₃).preimage continuous_subtype_val)
  exact this.index_ne_zero

theorem vol_ratio (V : HSp D) {K₁ K₂ : Subgroup (GL (Fin V.rank) (Lev.EAf D))} (h₁ : IsCO V K₁) (h₂ : IsCO V K₂)
    (ν : Measure (GfC V)) [ν.IsHaarMeasure] {μ μ' : Measure (GA D V)} (hμ : Lev.IsMeasLevDef V K₁ μ)
    (hμ' : Lev.IsMeasLevDef V K₂ μ') (x : ℝ≥0) (hx : μ = x • μ') :
    ν {g | Lev.finE V g.1 ∈ K₂} = ν {g | Lev.finE V g.1 ∈ K₁} * x := by
  obtain ⟨hLC, hSC, hT2, hB, hTG, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hB; haveI := hTG
  haveI : μ.IsHaarMeasure := hμ.1
  have h₃ : IsOpen (((K₁ ⊓ K₂).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := h₁.1.inter h₂.1
  have hA₁ : μ (K₁.comap (Lev.finE V)) = 1 := GlobalTheory.Mass.Levels.measure_comap_finE hμ
  have hA₂ : μ (K₂.comap (Lev.finE V)) = x := by
    rw [hx, Measure.smul_apply, GlobalTheory.Mass.Levels.measure_comap_finE hμ', ENNReal.smul_def, smul_eq_mul, mul_one]
  have n₁ := relIndex_ne_zero V h₁ h₃
  have n₂ := relIndex_ne_zero V h₂ h₃
  rw [relIndex_comap_fin] at n₁ n₂
  haveI : (((K₁ ⊓ K₂).comap (Lev.finE V)).subgroupOf (K₁.comap (Lev.finE V))).FiniteIndex := ⟨n₁⟩
  haveI : (((K₁ ⊓ K₂).comap (Lev.finE V)).subgroupOf (K₂.comap (Lev.finE V))).FiniteIndex := ⟨n₂⟩
  have e₁ := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure _ _ (Subgroup.comap_mono inf_le_left) h₃.measurableSet μ
  have e₂ := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure _ _ (Subgroup.comap_mono inf_le_right) h₃.measurableSet μ
  rw [hA₁] at e₁
  rw [hA₂] at e₂
  have m₁ := relIndex_ne_zero V h₁ h₃
  have m₂ := relIndex_ne_zero V h₂ h₃
  haveI : ((((K₁ ⊓ K₂).comap ((Lev.finE V).comp (GfC V).subtype))).subgroupOf
    (K₁.comap ((Lev.finE V).comp (GfC V).subtype))).FiniteIndex := ⟨m₁⟩
  haveI : ((((K₁ ⊓ K₂).comap ((Lev.finE V).comp (GfC V).subtype))).subgroupOf
    (K₂.comap ((Lev.finE V).comp (GfC V).subtype))).FiniteIndex := ⟨m₂⟩
  have f₁ := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure _ _ (Subgroup.comap_mono inf_le_left)
    (isOpen_comap_fin V h₃).measurableSet ν
  have f₂ := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure _ _ (Subgroup.comap_mono inf_le_right)
    (isOpen_comap_fin V h₃).measurableSet ν
  rw [relIndex_comap_fin] at f₁ f₂
  change ν (K₂.comap ((Lev.finE V).comp (GfC V).subtype)) = ν (K₁.comap ((Lev.finE V).comp (GfC V).subtype)) * x
  rw [← f₁, ← f₂]
  have key : ∀ (p q a m X : ENNReal), p * m = 1 → q * m = X → q * a = p * a * X := by
    intro p q a m X h1 h2
    rw [← h2, ← mul_one (q * a), ← h1]
    ring
  exact key _ _ _ _ _ e₁ e₂

theorem vol_pos (V : HSp D) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))} (h : IsCO V K)
    (ν : Measure (GfC V)) [ν.IsHaarMeasure] : 0 < ν.real {g | Lev.finE V g.1 ∈ K} := by
  obtain ⟨hLC, hSC, hT2, hB, hTG, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hB; haveI := hTG
  refine ENNReal.toReal_pos ?_ ?_
  · exact ((isOpen_comap_fin V h.1).measure_pos ν ⟨1, one_mem _⟩).ne'
  · exact ((isCompact_comap_fin V h).measure_lt_top).ne

end GlobalTheory.CellLevel

namespace GlobalTheory.CellLevel

theorem pr_vol_of (hpr : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ), ∀ j ∈ idx D, ∀ (hj : j < D.R.m) (ν : Measure (GfC (ch.G.V (.top j)))),
    ν.IsHaarMeasure → ∃ c : ℝ, 0 < c ∧ ∀ t Φ β b, IsRep t ch.S.B s β b → ∀ hb : b j ∈ GfC _,
      ν.real (prSet ch.G j ⟨b j, hb⟩) = c * ν.real {g | Lev.finE (ch.G.V (.top j)) g.1 ∈ ch.S.toGridChoice.levTop t Φ β j hj}) : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ), ∀ j ∈ idx D, ∀ ν : Measure (GfC (ch.G.V (.top j))), ν.IsHaarMeasure →
    ∃ κ' : ℝ, 0 < κ' ∧ ∀ t Φ β b, IsRep t ch.S.B s β b → ∀ M M' : Vol ch.G, M.Is t → IsTermVol t ch.S.toGridChoice Φ β M' →
      ∀ x : ℝ≥0, M.ν (.top j) = x • M'.ν (.top j) → ∀ hb : b j ∈ GfC _, ν.real (prSet ch.G j ⟨b j, hb⟩) = κ' * x := by
  refine big_mono ?_ hpr
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch h s j hj ν hν
  have hjm : j < D.R.m := by
    simp only [idx, List.mem_range'_1] at hj
    omega
  have hj1 : 1 ≤ j := by
    simp only [idx, List.mem_range'_1] at hj
    omega
  obtain ⟨c, hc, hcb⟩ := h s j hj hjm ν hν
  have hMax : IsCO (ch.G.V (.top j)) (ch.G.levMax (.top j)) :=
    congLev_open_compact _ (ch.G.isV (X := .top j) (show j ≤ D.R.m by omega) (fun _ h => Node.noConfusion h)).sd.1
      (by simp)
  refine ⟨c * ν.real {g | Lev.finE (ch.G.V (.top j)) g.1 ∈ ch.G.levMax (.top j)}, mul_pos hc (vol_pos _ hMax ν), ?_⟩
  intro t Φ β b hb M M' hM hM' x hx hbj
  rw [hcb t Φ β b hb hbj]
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have h1 : Lev.IsMeasLevDef _ (ch.G.levMax (.top (j' + 1))) (M.ν (.top (j' + 1))) := by
    have := hM.vtx (.top (j' + 1)) (show j' + 1 ≤ D.R.m by omega)
    unfold Vol.IsAt at this
    rw [if_pos (show Node.neg D.R.m (.top (j' + 1)) = 0 from rfl)] at this
    exact this.1
  have h2 : Lev.IsMeasLevDef _ (ch.S.toGridChoice.levTop t Φ β (j' + 1) hjm) (M'.ν (.top (j' + 1))) := by
    have := hM'.1 (j' + 1) hjm
    unfold Vol.IsAt at this
    rw [if_pos (show Node.neg D.R.m (.top (j' + 1)) = 0 from rfl)] at this
    exact this.1
  have e := vol_ratio _ hMax (GridChoice.isCO_levTop _ _ t Φ β hjm) ν h1 h2 x hx
  simp only [Measure.real, e, ENNReal.toReal_mul, ENNReal.coe_toReal, mul_assoc]

end GlobalTheory.CellLevel

namespace GlobalTheory.CellLevel

theorem pr_vol : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ), ∀ j ∈ idx D, ∀ ν : Measure (GfC (ch.G.V (.top j))), ν.IsHaarMeasure →
    ∃ κ' : ℝ, 0 < κ' ∧ ∀ t Φ β b, IsRep t ch.S.B s β b → ∀ M M' : Vol ch.G, M.Is t → IsTermVol t ch.S.toGridChoice Φ β M' →
      ∀ x : ℝ≥0, M.ν (.top j) = x • M'.ν (.top j) → ∀ hb : b j ∈ GfC _, ν.real (prSet ch.G j ⟨b j, hb⟩) = κ' * x := pr_vol_of GlobalTheory.T.volume_periodProjectionSet_eq_familyLevel

end GlobalTheory.CellLevel
