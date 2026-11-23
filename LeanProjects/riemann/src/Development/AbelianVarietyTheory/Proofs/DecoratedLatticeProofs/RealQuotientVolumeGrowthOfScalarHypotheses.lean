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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexMulMeasureAdelicLevelSetStatement
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
namespace GlobalTheory.ChainTw.VolScale

theorem scale {D : D7} (V : HSp D)
    (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop)
    (hgood : ∀ ρ m, good ρ m → m.IsHaarMeasure) (K₁ K₀ : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (ν₁ ν₀ : Measure (GA D V)) :
    K₁ ≤ K₀ → K₀ ≤ UA D.sp.cm V.gram → K₁.relIndex K₀ ≠ 0 → MeasurableSet {g : GA D V | Lev.finE V g ∈ K₁} →
    Lev.IsMeasLevW V K₁ good ν₁ → Lev.IsMeasLevW V K₀ good ν₀ → ν₁ = (K₁.relIndex K₀ : ℝ≥0∞) • ν₀ := by
  intro hle hUA hne hmeas h₁ h₀
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := GlobalTheory.RealMeasOne.ginfC_facts V
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨hH₁, ⟨θ, hθ⟩, k1⟩ := h₁
  obtain ⟨⟨A, hA⟩, k1⟩ := k1 θ hθ
  obtain ⟨⟨m, hm⟩, k1⟩ := k1 A hA
  obtain ⟨hH₀, -, k0⟩ := h₀
  obtain ⟨-, k0⟩ := k0 θ hθ
  obtain ⟨-, k0⟩ := k0 A hA
  have k0 := k0 m hm
  haveI := hH₁
  haveI := hH₀
  let B : ∀ ρ : D.what₂.Tau, TopologicalSpace.PositiveCompacts (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) :=
    fun ρ => Classical.arbitrary _
  have hB : ∀ ρ, MeasurableSet (B ρ : Set (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2)) := fun ρ =>
    (B ρ).isCompact.measurableSet
  let S : Set (GA D V) := {h | ∀ ρ, ∃ b ∈ (B ρ : Set _), UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h}
  have hSc : IsClosed S := by
    have e : S = ⋂ ρ, (fun h => A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h) ⁻¹'
        ((fun b => UpqT.mat b * A ρ) '' (B ρ : Set (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2))) := by
      ext h
      simp only [Set.mem_iInter]
      exact Iff.rfl
    rw [e]
    refine isClosed_iInter fun ρ => IsClosed.preimage ?_ ?_
    · exact continuous_const.matrix_mul (GlobalTheory.Mem.VolExists.continuous_infMat (σ := D.sp.cm.sig) V.gram (hθ ρ))
    · exact ((B ρ).isCompact.image ((GlobalTheory.UpqTopology.continuous_mat).matrix_mul continuous_const)).isClosed
  have hS : MeasurableSet S := hSc.measurableSet
  let E : Set (GinfC V) := Subtype.val ⁻¹' S
  have hE : MeasurableSet E := measurable_subtype_coe hS
  have hpre : GlobalTheory.AutMult.toInf V ⁻¹' E = S := by
    ext h
    simp only [E, S, Set.mem_preimage, Set.mem_setOf_eq, GlobalTheory.RealMeasOne.infMat_toInf]
  have hset : ∀ K : Subgroup (GL (Fin V.rank) (Lev.EAf D)), {g : GA D V | Lev.finE V g ∈ K} ∩ GlobalTheory.AutMult.toInf V ⁻¹' E =
      {h | Lev.finE V h ∈ K ∧ ∀ ρ, ∃ b ∈ (B ρ : Set _), UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h} := by
    intro K
    rw [hpre]
    rfl
  have v1 : ν₁ ({g : GA D V | Lev.finE V g ∈ K₁} ∩ GlobalTheory.AutMult.toInf V ⁻¹' E) = ∏ ρ, m ρ (B ρ) :=
    (congrArg ν₁ (hset K₁)).trans (k1 m hm (fun ρ => B ρ) hB)
  have v0 : ν₀ ({g : GA D V | Lev.finE V g ∈ K₀} ∩ GlobalTheory.AutMult.toInf V ⁻¹' E) = ∏ ρ, m ρ (B ρ) :=
    (congrArg ν₀ (hset K₀)).trans (k0 (fun ρ => B ρ) hB)
  have hI := GlobalTheory.T.relIndex_mul_measure_adelicLevelSet D V ν₀ K₁ K₀ E hle hUA hne hmeas hE
  rw [v0] at hI
  have h0 : ∏ ρ, m ρ (B ρ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun ρ _ => by
    have := hgood ρ (m ρ) (hm ρ)
    exact (Measure.measure_pos_of_nonempty_interior (m ρ) (B ρ).interior_nonempty).ne'
  have ht : ∏ ρ, m ρ (B ρ) ≠ ⊤ := ENNReal.prod_ne_top fun ρ _ => by
    have := hgood ρ (m ρ) (hm ρ)
    exact (B ρ).isCompact.measure_lt_top.ne
  set x := ν₀ ({g : GA D V | Lev.finE V g ∈ K₁} ∩ GlobalTheory.AutMult.toInf V ⁻¹' E) with hx
  have hx0 : x ≠ 0 := fun h => h0 (by rw [← hI, h, mul_zero])
  have hxt : x ≠ ⊤ := fun h => ht (by rw [← hI, h]; exact ENNReal.mul_top (by exact_mod_cast hne))
  have e : ν₁ = ((Measure.haarScalarFactor ν₁ ν₀ : NNReal) : ENNReal) • ν₀ := Measure.isMulLeftInvariant_eq_smul ν₁ ν₀
  have e' := v1
  rw [e, Measure.smul_apply, smul_eq_mul, ← hI] at e'
  have hc : ((Measure.haarScalarFactor ν₁ ν₀ : NNReal) : ENNReal) = (K₁.relIndex K₀ : ℝ≥0∞) :=
    (ENNReal.mul_left_inj hx0 hxt).1 e'
  rw [e, hc]

theorem vol_step {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L₁ L₀ : LevDat D.host.E ℂ V.rank)
    (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop)
    (hgood : ∀ ρ m, good ρ m → m.IsHaarMeasure) (ν₁ ν₀ : Measure (GA D V)) (N : ℝ)
    (hle : lev D.sp.cm V.gram β L₁ ≤ lev D.sp.cm V.gram β L₀)
    (hN : (((lev D.sp.cm V.gram β L₁).relIndex (lev D.sp.cm V.gram β L₀) : ℕ) : ℝ) = N) (hN0 : 0 < N)
    (hmeas : MeasurableSet {g : GA D V | Lev.finE V g ∈ lev D.sp.cm V.gram β L₁})
    (h₁ : Lev.IsMeasLevW V (lev D.sp.cm V.gram β L₁) good ν₁) (h₀ : Lev.IsMeasLevW V (lev D.sp.cm V.gram β L₀) good ν₀) :
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ V ν₁ = GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ V ν₀ * N ∧ 0 < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ V ν₁ := by
  have hne : (lev D.sp.cm V.gram β L₁).relIndex (lev D.sp.cm V.gram β L₀) ≠ 0 := by
    intro h0; rw [h0, Nat.cast_zero] at hN; linarith
  have e := scale V good hgood _ _ ν₁ ν₀ hle lev_le_UA hne hmeas h₁ h₀
  refine ⟨?_, ?_⟩
  · rw [e]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ
    have e2 : GlobalTheory.AutomorphicL2Unitary.autMeasure V (((lev D.sp.cm V.gram β L₁).relIndex (lev D.sp.cm V.gram β L₀) : ℝ≥0∞) • ν₀) =
        ((lev D.sp.cm V.gram β L₁).relIndex (lev D.sp.cm V.gram β L₀) : ℝ≥0∞) • GlobalTheory.AutomorphicL2Unitary.autMeasure V ν₀ :=
      GlobalTheory.AutomorphicL2Unitary.quotMeasure_smul _
    rw [e2, measureReal_ennreal_smul_apply, ← hN, ENNReal.toReal_natCast, mul_comm]
  · haveI := h₁.1
    exact GlobalTheory.RallisIP.Model.vol_pos ν₁

theorem idxQ_pos {D : D7} (PP : Pl D.host.E) (j : ℕ) : 0 < idxQ PP j := by
  have hq : (0 : ℝ) < (Ideal.absNorm PP.asIdeal : ℝ) := by
    have := HeightOneSpectrum.one_lt_absNorm PP
    exact_mod_cast (Nat.zero_lt_one.trans this)
  unfold idxQ
  exact div_pos (mul_pos (pow_pos hq _) (RModel.zinv_pos PP _ _)) (mul_pos (RModel.zinv_pos PP _ _) (RModel.zinv_pos PP _ _))

theorem rVol_of_given : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F →
    (∀ h : RangeX R, RChain R h) → RangeX R → RVol R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hC hR t
  have hQ0 : (twR R A.μ0).Q = ∅ := RModel.Q_base R hG.core.lev
  have hprod : ∀ j, 0 < ∏ PP ∈ R.Q t, idxQ PP j := fun j => Finset.prod_pos fun PP _ => idxQ_pos PP j
  refine ⟨fun j hj => ?_, ?_⟩
  · have hS := (hC hR t).2.1 j hj
    obtain ⟨hr0, hL0, -⟩ := (hC hR A.μ0).2.1 j hj
    rw [hQ0] at hL0
    obtain ⟨good, hgood, hW⟩ := GlobalTheory.RealMeasOne.models_good R hG.core.models j hj
    obtain ⟨hle, hN⟩ := GlobalTheory.T.twistedLevel_relIndex_eq_prod_parabolicIndices D (comR R t) (twR R t) j (stY R t j) (hC hR t).1 hj.le hS hr0 R.chi (R.xiR A.μ0)
    have e : Lev.datY (stY R t j).V.rank D.R.r D.R.t j hr0 (twR R t).Pg ∅ (LevelP.triv _ _ _) R.chi (R.xiR A.μ0) Lev.Frm.B =
        R.datYt A.μ0 j R.triv := hL0.symm
    rw [e] at hle hN
    have hmeas := (GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D (comR R t) (twR R t) (hC hR t).1 j hj.le (stY R t j) hS).1
    exact vol_step (Yc D j) (R.βY j) (R.datYt t j R.triv) (R.datYt A.μ0 j R.triv) good hgood (R.νY t j) (R.νY A.μ0 j) _
      hle hN (hprod j) hmeas (hW t) (hW A.μ0)
  · have hS := (hC hR t).2.2.1
    obtain ⟨hr0, hL0, -⟩ := (hC hR A.μ0).2.2.1
    rw [hQ0] at hL0
    obtain ⟨hle, hN⟩ := GlobalTheory.T.twistedLevel_relIndex_eq_prod_parabolicIndices D (comR R t) (twR R t) D.R.m (stX R t) (hC hR t).1 le_rfl hS hr0 R.chi (R.xiR A.μ0)
    have e : Lev.datY (stX R t).V.rank D.R.r D.R.t D.R.m hr0 (twR R t).Pg ∅ (LevelP.triv _ _ _) R.chi (R.xiR A.μ0) Lev.Frm.B =
        R.datXt A.μ0 := hL0.symm
    rw [e] at hle hN
    have hmeas := (GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D (comR R t) (twR R t) (hC hR t).1 D.R.m le_rfl (stX R t) hS).1
    have h := vol_step D.sp.X' R.βX (R.datXt t) (R.datXt A.μ0) (fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m)
      (fun _ _ hm => hm.1) (R.νX t) (R.νX A.μ0) _ hle hN (hprod D.R.m) hmeas (hG.core.models.νX t).1 (hG.core.models.νX A.μ0).1
    exact ⟨h.1, h.2⟩

end GlobalTheory.ChainTw.VolScale

end
