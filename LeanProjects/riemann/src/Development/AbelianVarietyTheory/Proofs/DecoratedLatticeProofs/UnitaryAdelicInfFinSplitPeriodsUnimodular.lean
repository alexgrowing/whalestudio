import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientIntegrationFormulaDiscreteSubgroupLeft
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceCmHostAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentAnisotropicProjectionEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiGroupSplitRealFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupSplitRealFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiGroupHaarIsMulRightInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupHaarIsMulRightInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdelicSplit

open scoped NNReal ENNReal

section General

variable {A B : Type} [Group A] [Group B] [TopologicalSpace A] [TopologicalSpace B]
  [IsTopologicalGroup A] [IsTopologicalGroup B] [LocallyCompactSpace A] [LocallyCompactSpace B]
  [SecondCountableTopology A] [SecondCountableTopology B] [T2Space A] [T2Space B]
  [MeasurableSpace A] [MeasurableSpace B] [BorelSpace A] [BorelSpace B]

theorem rightInv_of_prod (h : ∀ μ : Measure (A × B), μ.IsHaarMeasure → μ.IsMulRightInvariant)
    (ν : Measure B) (hν : ν.IsHaarMeasure) : ν.IsMulRightInvariant := by
  refine ⟨fun b => ?_⟩
  let μA : Measure A := Measure.haar
  haveI := h (μA.prod ν) inferInstance
  set c := Measure.haarScalarFactor (ν.map (· * b)) ν
  have hc : ν.map (· * b) = c • ν := Measure.isMulLeftInvariant_eq_smul _ _
  have h1 : (μA.prod ν).map (· * ((1 : A), b)) = μA.prod (ν.map (· * b)) := by
    have e : (fun x : A × B => x * ((1 : A), b)) = Prod.map id (· * b) := by
      funext x
      simp [Prod.ext_iff]
    rw [e, ← Measure.map_prod_map _ _ measurable_id (measurable_mul_const b), Measure.map_id]
  have h3 : μA.prod ν = (c : ℝ≥0∞) • μA.prod ν := by
    rw [← Measure.prod_smul_right, ← ENNReal.smul_def, ← hc, ← h1, map_mul_right_eq_self]
  obtain K : TopologicalSpace.PositiveCompacts (A × B) := Classical.arbitrary _
  have hpos : 0 < μA.prod ν K := Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty
  have hfin : μA.prod ν K < ⊤ := K.isCompact.measure_lt_top
  have h4 := congrArg (fun m : Measure (A × B) => m K) h3
  simp only [Measure.smul_apply, smul_eq_mul] at h4
  have h5 : (c : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj hpos.ne' hfin.ne).1 (h4.symm.trans (one_mul _).symm)
  rw [hc, ENNReal.smul_def, h5, one_smul]

end General

section Restr

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def restrEquiv (P Q R : Subgroup G) (e : P × Q ≃ₜ* G) (he : ∀ p, e p = p.1.1 * p.2.1)
    (hs : ∀ a ∈ P, ∀ b ∈ Q, a * b ∈ R → a ∈ R ∧ b ∈ R) :
    R.subgroupOf P × R.subgroupOf Q ≃ₜ* R where
  toFun x := ⟨e (x.1.1, x.2.1), by
    rw [he]; exact R.mul_mem (Subgroup.mem_subgroupOf.1 x.1.2) (Subgroup.mem_subgroupOf.1 x.2.2)⟩
  invFun r :=
    have hr : ((e.symm r.1).1 : G) * (e.symm r.1).2 ∈ R := by rw [← he, e.apply_symm_apply]; exact r.2
    (⟨(e.symm r.1).1, Subgroup.mem_subgroupOf.2 (hs _ (e.symm r.1).1.2 _ (e.symm r.1).2.2 hr).1⟩,
     ⟨(e.symm r.1).2, Subgroup.mem_subgroupOf.2 (hs _ (e.symm r.1).1.2 _ (e.symm r.1).2.2 hr).2⟩)
  left_inv x := by
    have h : e.symm (e (x.1.1, x.2.1)) = (x.1.1, x.2.1) := e.symm_apply_apply _
    ext
    · exact congrArg (fun p => (p.1 : G)) h
    · exact congrArg (fun p => (p.2 : G)) h
  right_inv r := Subtype.ext (e.apply_symm_apply r.1)
  map_mul' x y := Subtype.ext (by
    change e ((x * y).1.1, (x * y).2.1) = e (x.1.1, x.2.1) * e (y.1.1, y.2.1)
    rw [← map_mul]; rfl)
  continuous_toFun := by
    refine Continuous.subtype_mk (e.continuous.comp ?_) _
    exact (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    have h0 : Continuous fun r : R => e.symm r.1 := e.symm.continuous.comp continuous_subtype_val
    exact (Continuous.subtype_mk (continuous_fst.comp h0) _).prodMk (Continuous.subtype_mk (continuous_snd.comp h0) _)

variable [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem rightInv_restr (P Q R : Subgroup G) (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G))
    (hR : IsClosed (R : Set G)) (e : P × Q ≃ₜ* G) (he : ∀ p, e p = p.1.1 * p.2.1)
    (hs : ∀ a ∈ P, ∀ b ∈ Q, a * b ∈ R → a ∈ R ∧ b ∈ R)
    (hu : ∀ μ : Measure R, μ.IsHaarMeasure → μ.IsMulRightInvariant) :
    ∀ ν : Measure (R.subgroupOf Q), ν.IsHaarMeasure → ν.IsMulRightInvariant := by
  haveI : LocallyCompactSpace P := hP.locallyCompactSpace
  haveI : LocallyCompactSpace Q := hQ.locallyCompactSpace
  haveI : LocallyCompactSpace R := hR.locallyCompactSpace
  have hRP : IsClosed ((R.subgroupOf P : Subgroup P) : Set P) := hR.preimage continuous_subtype_val
  have hRQ : IsClosed ((R.subgroupOf Q : Subgroup Q) : Set Q) := hR.preimage continuous_subtype_val
  haveI : LocallyCompactSpace (R.subgroupOf P) := hRP.locallyCompactSpace
  haveI : LocallyCompactSpace (R.subgroupOf Q) := hRQ.locallyCompactSpace
  intro ν hν
  refine rightInv_of_prod (A := R.subgroupOf P) (fun μ hμ => ?_) ν hν
  haveI := hμ
  exact GlobalTheory.UpqUnimodular.isMulRightInvariant_of_continuousMulEquiv (restrEquiv P Q R e he hs) μ
    (hu _ (ContinuousMulEquiv.isHaarMeasure_map μ (restrEquiv P Q R e he hs)))

end Restr

section Adelic

open GlobalTheory.AdelicU

variable {D : D7}

theorem ofInf_projInf_of_mem (V : HSp D) {a : GA D V} (ha : a ∈ GinfC V) :
    ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram a) = a := by
  have h := ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig V.gram a
  rwa [mem_infPts.1 ha, map_one, mul_one] at h

theorem ofFin_projFin_of_mem (V : HSp D) {b : GA D V} (hb : b ∈ GfC V) :
    ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram b) = b := by
  have h := ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig V.gram b
  rwa [mem_finPts.1 hb, map_one, one_mul] at h

theorem commute_GinfC_GfC (V : HSp D) {a b : GA D V} (ha : a ∈ GinfC V) (hb : b ∈ GfC V) : a * b = b * a := by
  rw [← ofInf_projInf_of_mem V ha, ← ofFin_projFin_of_mem V hb]
  exact commute_ofInf_ofFin _ _ _ _

def splitEquiv (V : HSp D) : GinfC V × GfC V ≃ₜ* GA D V where
  toFun p := p.1.1 * p.2.1
  invFun g := (⟨ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g), mem_infPts.2 (by simp)⟩,
    ⟨ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram g), mem_finPts.2 (by simp)⟩)
  left_inv p := by
    have h1 : projInf D.sp.cm.sig V.gram p.2.1 = 1 := mem_finPts.1 p.2.2
    have h2 : projFin D.sp.cm.sig V.gram p.1.1 = 1 := mem_infPts.1 p.1.2
    ext
    · change ofInf _ _ (projInf _ _ (p.1.1 * p.2.1)) = p.1.1
      rw [map_mul, h1, mul_one, ofInf_projInf_of_mem V p.1.2]
    · change ofFin _ _ (projFin _ _ (p.1.1 * p.2.1)) = p.2.1
      rw [map_mul, h2, one_mul, ofFin_projFin_of_mem V p.2.2]
  right_inv g := ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig V.gram g
  map_mul' p q := by
    change p.1.1 * q.1.1 * (p.2.1 * q.2.1) = p.1.1 * p.2.1 * (q.1.1 * q.2.1)
    rw [mul_assoc, ← mul_assoc q.1.1, commute_GinfC_GfC V q.1.2 p.2.2, mul_assoc, mul_assoc]
  continuous_toFun := (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_invFun :=
    (((continuous_ofInf _ _).comp (continuous_projInf _ _)).subtype_mk _).prodMk
      (((continuous_ofFin _ _).comp (continuous_projFin _ _)).subtype_mk _)

theorem splitEquiv_apply (V : HSp D) (p : GinfC V × GfC V) : splitEquiv V p = p.1.1 * p.2.1 := rfl

theorem isClosed_GinfC' (V : HSp D) : IsClosed (GinfC V : Set (GA D V)) := isClosed_infPts _ _
theorem isClosed_GfC' (V : HSp D) : IsClosed (GfC V : Set (GA D V)) := isClosed_finPts _ _

end Adelic

theorem adelic_split : ∀ (D : D7) (V : HSp D), IsClosed (GinfC V : Set (GA D V)) ∧ IsClosed (GfC V : Set (GA D V)) ∧ (∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b = b * a) ∧ (∃ e : (GinfC V × GfC V) ≃ₜ GA D V, ∀ p, e p = p.1 * p.2) ∧ (∀ μ : Measure (GfC V), μ.IsHaarMeasure → μ.IsMulRightInvariant) ∧ ∀ (V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), ((∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b ∈ jacGrp d → a ∈ jacGrp d ∧ b ∈ jacGrp d) ∧ (∀ μ : Measure (jacGrp d), μ.IsHaarMeasure → μ.IsInvInvariant) ∧ ∀ μ : Measure ((jacGrp d).subgroupOf (GfC V)), μ.IsHaarMeasure → μ.IsInvInvariant) ∧ ∀ (A L : HSp D) (o : OrthDec V₀ A L), (∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b ∈ besGrp d o → a ∈ besGrp d o ∧ b ∈ besGrp d o) ∧ (∀ μ : Measure (besGrp d o), μ.IsHaarMeasure → μ.IsInvInvariant) ∧ ∀ μ : Measure ((besGrp d o).subgroupOf (GfC V)), μ.IsHaarMeasure → μ.IsInvInvariant := by
  intro D V
  have hi := isClosed_GinfC' V
  have hf := isClosed_GfC' V
  haveI : LocallyCompactSpace (GinfC V) := hi.locallyCompactSpace
  haveI : LocallyCompactSpace (GfC V) := hf.locallyCompactSpace
  refine ⟨hi, hf, fun a ha b hb => commute_GinfC_GfC V ha hb, ⟨(splitEquiv V).toHomeomorph, fun p => rfl⟩,
    fun μ hμ => rightInv_of_prod (A := GinfC V) (fun m hm => ?_) μ hμ, fun V₀ ρ d => ?_⟩
  · haveI := hm
    exact GlobalTheory.UpqUnimodular.isMulRightInvariant_of_continuousMulEquiv (splitEquiv V) m
      (GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V _ inferInstance)
  have hJ := GlobalTheory.jacGrp_isClosed D V V₀ ρ d
  haveI : LocallyCompactSpace (jacGrp d) := hJ.locallyCompactSpace
  refine ⟨⟨GlobalTheory.T.fourierJacobiGroup_split_real_finite D V V₀ ρ d, fun μ hμ => ?_, fun μ hμ => ?_⟩, fun A L o => ?_⟩
  · haveI := hμ
    haveI := GlobalTheory.T.fourierJacobiGroup_haar_isMulRightInvariant D V V₀ ρ d μ hμ
    exact GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ
  · have hc : IsClosed (((jacGrp d).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) :=
      hJ.preimage continuous_subtype_val
    haveI : LocallyCompactSpace ((jacGrp d).subgroupOf (GfC V)) := hc.locallyCompactSpace
    haveI := hμ
    haveI := rightInv_restr (GinfC V) (GfC V) (jacGrp d) hi hf hJ (splitEquiv V) (splitEquiv_apply V)
      (GlobalTheory.T.fourierJacobiGroup_split_real_finite D V V₀ ρ d) (GlobalTheory.T.fourierJacobiGroup_haar_isMulRightInvariant D V V₀ ρ d) μ hμ
    exact GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ
  have hB := GlobalTheory.BesClosed.besGrp_isClosed D V V₀ A L ρ d o
  haveI : LocallyCompactSpace (besGrp d o) := hB.locallyCompactSpace
  refine ⟨GlobalTheory.T.besselGroup_split_real_finite D V V₀ A L ρ d o, fun μ hμ => ?_, fun μ hμ => ?_⟩
  · haveI := hμ
    haveI := GlobalTheory.T.besselGroup_haar_isMulRightInvariant D V V₀ A L ρ d o μ hμ
    exact GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ
  · have hc : IsClosed (((besGrp d o).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) :=
      hB.preimage continuous_subtype_val
    haveI : LocallyCompactSpace ((besGrp d o).subgroupOf (GfC V)) := hc.locallyCompactSpace
    haveI := hμ
    haveI := rightInv_restr (GinfC V) (GfC V) (besGrp d o) hi hf hB (splitEquiv V) (splitEquiv_apply V)
      (GlobalTheory.T.besselGroup_split_real_finite D V V₀ A L ρ d o) (GlobalTheory.T.besselGroup_haar_isMulRightInvariant D V V₀ A L ρ d o) μ hμ
    exact GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ

end GlobalTheory.AdelicSplit
