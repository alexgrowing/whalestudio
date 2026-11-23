import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepExactNS
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMeasureUniformInTupleOfThetaLiftScalar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageFiniteLevelEqProductLocalLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedLevelRelIndexEqProdParabolicIndicesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClPlusAndExistsCoords
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PeterssonLiftSmulMeasure
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnderEqOfConj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open scoped NNReal ENNReal

noncomputable section

open scoped Pointwise

namespace GlobalTheory.LevelIndexMeasure

theorem relIndex_mul_measure_preimage {G Q R : Type*} [Group G] [Group Q] [Group R] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (φ : G →* Q) (ψ : G →* R) (N : Subgroup G) (hN : ∀ n ∈ N, ψ n = 1)
    (H₁ H₀ : Subgroup Q) (h10 : H₁ ≤ H₀) (hsurj : H₀ ≤ N.map φ) (hfi : H₁.relIndex H₀ ≠ 0) (E : Set R)
    (hS : MeasurableSet (φ ⁻¹' (H₁ : Set Q) ∩ ψ ⁻¹' E)) :
    (H₁.relIndex H₀ : ℝ≥0∞) * μ (φ ⁻¹' (H₁ : Set Q) ∩ ψ ⁻¹' E) = μ (φ ⁻¹' (H₀ : Set Q) ∩ ψ ⁻¹' E) := by
  haveI : (H₁.subgroupOf H₀).FiniteIndex := ⟨hfi⟩
  obtain ⟨s, hs, -⟩ := (H₁.subgroupOf H₀).exists_isComplement_left 1
  have hs' : Finite s := hs.finite_left_iff.mpr inferInstance
  have hl : ∀ a : s, ∃ n ∈ N, φ n = ((a.val : H₀) : Q) := fun a => hsurj a.val.2
  choose lift hlN hlφ using hl
  set S₁ := φ ⁻¹' (H₁ : Set Q) ∩ ψ ⁻¹' E
  have hU : (⋃ a : s, lift a • S₁) = φ ⁻¹' (H₀ : Set Q) ∩ ψ ⁻¹' E := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_smul_set, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe, S₁, smul_eq_mul]
    constructor
    · rintro ⟨a, y, ⟨hy1, hy2⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [map_mul, hlφ]; exact H₀.mul_mem a.val.2 (h10 hy1)
      · rw [map_mul, hN _ (hlN a), one_mul]; exact hy2
    · rintro ⟨hx1, hx2⟩
      obtain ⟨⟨b, h⟩, hbh, -⟩ := hs.existsUnique ⟨φ x, hx1⟩
      refine ⟨b, (lift b)⁻¹ * x, ⟨?_, ?_⟩, by group⟩
      · have e : ((b : H₀) : Q) * ((h : H₀) : Q) = φ x := congrArg Subtype.val hbh
        rw [map_mul, map_inv, hlφ, ← e, inv_mul_cancel_left]
        exact Subgroup.mem_subgroupOf.mp h.2
      · rw [map_mul, map_inv, hN _ (hlN b), inv_one, one_mul]; exact hx2
  have hdisj : Pairwise (Function.onFun Disjoint fun a : s => lift a • S₁) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨y1, ⟨hy1, -⟩, rfl⟩ ⟨y2, ⟨hy2, -⟩, he⟩
    apply hab
    simp only [smul_eq_mul] at he
    have he' := congrArg φ he
    rw [map_mul, map_mul, hlφ, hlφ] at he'
    have hh1' : (⟨φ y1, h10 hy1⟩ : H₀) ∈ H₁.subgroupOf H₀ := Subgroup.mem_subgroupOf.mpr hy1
    have hh2' : (⟨φ y2, h10 hy2⟩ : H₀) ∈ H₁.subgroupOf H₀ := Subgroup.mem_subgroupOf.mpr hy2
    have e : (a.val : H₀) * ⟨φ y1, h10 hy1⟩ = (b.val : H₀) * ⟨φ y2, h10 hy2⟩ := Subtype.ext he'.symm
    have := (hs.existsUnique ((a.val : H₀) * ⟨φ y1, h10 hy1⟩)).unique
      (y₁ := (a, ⟨_, hh1'⟩)) (y₂ := (b, ⟨_, hh2'⟩)) rfl e.symm
    exact congrArg Prod.fst this
  calc (H₁.relIndex H₀ : ℝ≥0∞) * μ S₁ = ∑' a : s, μ (lift a • S₁) := by
        simp [measure_smul, hs.encard_left, Subgroup.relIndex]
    _ = μ (⋃ a : s, lift a • S₁) := (measure_iUnion hdisj fun a => hS.const_smul _).symm
    _ = _ := by rw [hU]

end GlobalTheory.LevelIndexMeasure

namespace GlobalTheory.LevelIndexMeasure

variable {D : D7}

theorem relIndex_mul_measure_levelSet : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)) [ν.IsMulLeftInvariant] (K₁ K₀ : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (E : Set (GinfC V)), K₁ ≤ K₀ → K₀ ≤ UA D.sp.cm V.gram → K₁.relIndex K₀ ≠ 0 → MeasurableSet {g : GA D V | Lev.finE V g ∈ K₁} → MeasurableSet E → (K₁.relIndex K₀ : ℝ≥0∞) * ν ({g : GA D V | Lev.finE V g ∈ K₁} ∩ GlobalTheory.AutMult.toInf V ⁻¹' E) = ν ({g : GA D V | Lev.finE V g ∈ K₀} ∩ GlobalTheory.AutMult.toInf V ⁻¹' E) := by
  intro D V ν _ K₁ K₀ E h10 h0U hfi hK₁ hE
  obtain ⟨i1, -, -, -, i5, -, -, i8⟩ := GlobalTheory.RealMeasOne.ginfC_facts V
  have hmeas : Measurable (GlobalTheory.AutMult.toInf V) := (GlobalTheory.AutMult.continuous_toInf V).measurable
  have hsurj : K₀ ≤ (GfC V).map (Lev.finE V) := by
    rw [← GlobalTheory.FunObj.map_levA V h0U]
    exact Subgroup.map_mono inf_le_left
  exact relIndex_mul_measure_preimage ν (Lev.finE V) (GlobalTheory.AutMult.toInf V) (GfC V)
    (fun n hn => (GlobalTheory.ChainOnto.HaarInf.toInf_eq_one_iff V n).2 hn) K₁ K₀ h10 hsurj hfi E (hK₁.inter (hmeas hE))

end GlobalTheory.LevelIndexMeasure
