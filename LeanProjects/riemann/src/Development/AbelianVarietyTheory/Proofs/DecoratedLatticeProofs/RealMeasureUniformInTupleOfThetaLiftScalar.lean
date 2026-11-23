import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepExactNS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageFiniteLevelEqProductLocalLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PushforwardHaarRealPointsTimesLevel
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureSecond
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.RealMeasOne

variable {D : D7}

theorem ginfC_facts (V : HSp D) : IsTopologicalGroup (GA D V) ∧ LocallyCompactSpace (GA D V) ∧
    SecondCountableTopology (GA D V) ∧ T2Space (GA D V) ∧ BorelSpace (GA D V) ∧ LocallyCompactSpace (GinfC V) ∧
    SecondCountableTopology (GinfC V) ∧ BorelSpace (GinfC V) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  exact ⟨i1, i2, i3, i4, i5, i6.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    Topology.IsInducing.subtypeVal.secondCountableTopology, Subtype.borelSpace _⟩

theorem eq_map_of_lev {V : HSp D} (K : Subgroup (GA D V)) (hK : K ≤ GfC V) (A : Set (GA D V)) (ν : Measure (GA D V))
    (mR : Measure (GinfC V)) (hH : mR.IsHaarMeasure)
    (h : ∀ (f : GinfC V → ℂ) (F : GA D V → ℂ), Integrable f mR → (∀ b : GinfC V, ∀ κ ∈ K, F ((b : GA D V) * κ) = f b) →
      IntegrableOn F A ν ∧ ∫ g in A, F g ∂ν = ∫ b, f b ∂mR) :
    mR = Measure.map (GlobalTheory.AutMult.toInf V) (ν.restrict A) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := ginfC_facts V
  haveI := hH
  have hmeas : Measurable (GlobalTheory.AutMult.toInf V) := (GlobalTheory.AutMult.continuous_toInf V).measurable

  have hfin : ∀ G : Set (GinfC V), MeasurableSet G → mR G < ⊤ →
      mR G = Measure.map (GlobalTheory.AutMult.toInf V) (ν.restrict A) G := by
    intro G hG hGf
    have hS : MeasurableSet (GlobalTheory.AutMult.toInf V ⁻¹' G) := hmeas hG
    have hf : Integrable (G.indicator fun _ => (1 : ℂ)) mR :=
      (integrable_indicator_iff hG).2 ((integrableOn_const_iff (by simp)).2 (Or.inr hGf))
    obtain ⟨hi, he⟩ := h (G.indicator fun _ => (1 : ℂ)) ((GlobalTheory.AutMult.toInf V ⁻¹' G).indicator fun _ => (1 : ℂ)) hf
      (fun b κ hκ => by
        have h1 : GlobalTheory.AutMult.toInf V ((b : GA D V) * κ) = b := by
          rw [map_mul, GlobalTheory.AutMult.toInf_coe, (GlobalTheory.ChainOnto.HaarInf.toInf_eq_one_iff V κ).2 (hK hκ), mul_one]
        classical
        rw [Set.indicator_apply, Set.indicator_apply, Set.mem_preimage, h1])
    have hi' : ν.restrict A (GlobalTheory.AutMult.toInf V ⁻¹' G) < ⊤ := by
      have := ((integrable_indicator_iff hS).1 hi)
      rcases (integrableOn_const_iff (by simp)).1 this with h0 | h0
      · simp at h0
      · exact h0
    rw [integral_indicator_const _ hS, integral_indicator_const _ hG] at he
    have he' : (ν.restrict A).real (GlobalTheory.AutMult.toInf V ⁻¹' G) = mR.real G := by
      simpa using he
    rw [Measure.map_apply hmeas hG]
    exact ((ENNReal.toReal_eq_toReal_iff' hGf.ne hi'.ne).1 he'.symm)
  refine Measure.ext fun G hG => ?_
  have hU : ⋃ n, G ∩ spanningSets mR n = G := by rw [← Set.inter_iUnion, iUnion_spanningSets, Set.inter_univ]
  have hmono : Monotone fun n => G ∩ spanningSets mR n := fun a b hab =>
    Set.inter_subset_inter_right _ (monotone_spanningSets mR hab)
  rw [← hU, hmono.measure_iUnion, hmono.measure_iUnion]
  refine iSup_congr fun n => hfin _ (hG.inter (measurableSet_spanningSets mR n)) ?_
  exact (measure_mono Set.inter_subset_right).trans_lt (measure_spanningSets_lt_top mR n)

end GlobalTheory.RealMeasOne

namespace GlobalTheory.RealMeasOne

variable {D : D7}

theorem infMat_toInf (V : HSp D) (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g : GA D V) :
    infMat D.sp.cm.sig V.gram φ (GlobalTheory.AutMult.toInf V g : GA D V) = infMat D.sp.cm.sig V.gram φ g := by
  conv_rhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.TensRep.infMat_of_mem_fin V φ (GlobalTheory.AutMult.toFin V g).2, Matrix.mul_one]

theorem eq_of_measLevW {V : HSp D}
    {good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop}
    (hgood : ∀ ρ m, good ρ m → m.IsHaarMeasure)
    {K₁ K₂ : Subgroup (GL (Fin V.rank) (Lev.EAf D))} {ν₁ ν₂ : Measure (GA D V)}
    (h₁ : Lev.IsMeasLevW V K₁ good ν₁) (h₂ : Lev.IsMeasLevW V K₂ good ν₂)
    (m₁ m₂ : Measure (GinfC V)) (hH₁ : m₁.IsHaarMeasure) (hH₂ : m₂.IsHaarMeasure)
    (e₁ : m₁ = Measure.map (GlobalTheory.AutMult.toInf V) (ν₁.restrict {g | Lev.finE V g ∈ K₁}))
    (e₂ : m₂ = Measure.map (GlobalTheory.AutMult.toInf V) (ν₂.restrict {g | Lev.finE V g ∈ K₂})) : m₁ = m₂ := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := ginfC_facts V
  haveI := hH₁
  haveI := hH₂
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨-, ⟨θ, hθ⟩, h1⟩ := h₁
  obtain ⟨⟨A, hA⟩, h1⟩ := h1 θ hθ
  obtain ⟨⟨m, hm⟩, h1⟩ := h1 A hA
  obtain ⟨-, -, h2⟩ := h₂
  obtain ⟨-, h2⟩ := h2 θ hθ
  obtain ⟨-, h2⟩ := h2 A hA
  have h2 := h2 m hm
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
    simp only [E, S, Set.mem_preimage, Set.mem_setOf_eq, infMat_toInf]
  have hval : ∀ (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (ν : Measure (GA D V)),
      Measure.map (GlobalTheory.AutMult.toInf V) (ν.restrict {g | Lev.finE V g ∈ K}) E =
        ν {h | Lev.finE V h ∈ K ∧ ∀ ρ, ∃ b ∈ (B ρ : Set _), UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h} := by
    intro K ν
    rw [Measure.map_apply (GlobalTheory.AutMult.continuous_toInf V).measurable hE, hpre, Measure.restrict_apply hS]
    congr 1
    ext h
    exact and_comm
  have v1 : m₁ E = ∏ ρ, m ρ (B ρ) := by rw [e₁, hval]; exact h1 m hm (fun ρ => B ρ) hB
  have v2 : m₂ E = ∏ ρ, m ρ (B ρ) := by rw [e₂, hval]; exact h2 (fun ρ => B ρ) hB
  have h0 : ∏ ρ, m ρ (B ρ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun ρ _ => by
    have := hgood ρ (m ρ) (hm ρ)
    exact (Measure.measure_pos_of_nonempty_interior (m ρ) (B ρ).interior_nonempty).ne'
  have ht : ∏ ρ, m ρ (B ρ) ≠ ⊤ := ENNReal.prod_ne_top fun ρ _ => by
    have := hgood ρ (m ρ) (hm ρ)
    exact (B ρ).isCompact.measure_lt_top.ne
  have e : m₂ = ((Measure.haarScalarFactor m₂ m₁ : NNReal) : ENNReal) • m₁ := Measure.isMulLeftInvariant_eq_smul m₂ m₁
  have e' := v2
  rw [e, Measure.smul_apply, v1, smul_eq_mul] at e'
  have hc : ((Measure.haarScalarFactor m₂ m₁ : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj h0 ht).1 (e'.trans (one_mul _).symm)
  rw [e, hc, one_smul]

end GlobalTheory.RealMeasOne

namespace GlobalTheory.RealMeasOne

theorem models_good {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hM : R.IsModels) (j : ℕ)
    (hj : j < D.R.m) :
    ∃ good : ∀ ρ : D.what₂.Tau, Measure (UpqT ((Yc D j).sig (tauE D ρ)).1 ((Yc D j).sig (tauE D ρ)).2) → Prop,
      (∀ ρ m, good ρ m → m.IsHaarMeasure) ∧
      ∀ t, Lev.IsMeasLevW (Yc D j) (lev D.sp.cm (Yc D j).gram (R.βY j) (R.datYt t j R.triv)) good (R.νY t j) := by
  rcases Nat.lt_or_ge (j + 1) D.R.m with h | h
  · exact ⟨fun _ m => Lev.IsMinf m, fun _ _ hm => hm.1, fun t => (hM.νY t j h).1⟩
  · obtain rfl : j = D.R.m - 1 := by omega
    exact ⟨fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m, fun _ _ hm => hm.1, fun t => (hM.νY' t).1⟩

theorem one_real_measure : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F →
    (∀ h : RangeX R, RChain R h) → RangeX R → RMeas R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hC hR j hj
  by_cases hT : Nonempty T
  swap
  · exact ⟨0, fun t => (hT ⟨t⟩).elim⟩
  obtain ⟨t₀⟩ := hT
  have hlev : ∀ t, ∃ mR, IsLevMeas (stY R t j) mR := fun t =>
    (GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D (comR R t) (twR R t) (hC hR t).1 j hj.le (stY R t j) ((hC hR t).2.1 j hj)).2.2.2.2.2
  choose mR hmR using hlev
  obtain ⟨good, hgood, hW⟩ := models_good R hG.core.models j hj
  have hmap : ∀ t, mR t = Measure.map (GlobalTheory.AutMult.toInf (Yc D j))
      ((R.νY t j).restrict {g | Lev.finE (Yc D j) g ∈ lev D.sp.cm (Yc D j).gram (R.βY j) (R.datYt t j R.triv)}) := fun t => by
    exact eq_map_of_lev (Lev.levG (Yc D j) (R.βY j) (R.datYt t j R.triv)) inf_le_left _ _ (mR t) (hmR t).1 (hmR t).2
  refine ⟨mR t₀, fun t => ?_⟩
  have e : mR t = mR t₀ := by
    exact eq_of_measLevW hgood (hW t) (hW t₀) (mR t) (mR t₀) (hmR t).1 (hmR t₀).1 (hmap t) (hmap t₀)
  rw [← e]
  exact hmR t

end GlobalTheory.RealMeasOne

end
