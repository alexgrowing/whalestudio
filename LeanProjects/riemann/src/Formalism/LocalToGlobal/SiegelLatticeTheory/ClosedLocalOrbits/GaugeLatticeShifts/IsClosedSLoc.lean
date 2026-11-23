import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacExGoodOfN
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UpMatZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SigmaFiniteOfFcG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GroupFactorizationHolds

noncomputable section

open MeasureTheory Measure Topology
open scoped ENNReal NNReal
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HC

section Gen

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem comap_inv (S : Subgroup G) (hS : IsClosed (S : Set G)) (ν : Measure G) (hνc : ν (S : Set G)ᶜ = 0)
    (hνi : ∀ s ∈ S, ν.map (fun x => s * x) = ν) :
    (ν.comap (Subtype.val : S → G)).IsMulLeftInvariant ∧ (ν.comap (Subtype.val : S → G)).map Subtype.val = ν := by
  have he : MeasurableEmbedding (Subtype.val : S → G) := MeasurableEmbedding.subtype_coe hS.measurableSet
  refine ⟨⟨fun g => ?_⟩, ?_⟩
  · refine Measure.ext fun A hA => ?_
    rw [Measure.map_apply (measurable_const_mul g) hA, he.comap_apply, he.comap_apply]
    have hB : MeasurableSet (Subtype.val '' A : Set G) := he.measurableSet_image.2 hA
    have eset : (Subtype.val : S → G) '' ((fun x => g * x) ⁻¹' A) =
        (fun x => (g : G) * x) ⁻¹' (Subtype.val '' A) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨g * y, hy, rfl⟩
      · rintro ⟨a, ha, hax⟩
        have hx : x ∈ S := by
          have : x = (g : G)⁻¹ * (a : G) := by rw [hax]; group
          rw [this]; exact S.mul_mem (S.inv_mem g.2) a.2
        refine ⟨⟨x, hx⟩, ?_, rfl⟩
        have : g * (⟨x, hx⟩ : S) = a := Subtype.ext (by simpa using hax.symm)
        show g * (⟨x, hx⟩ : S) ∈ A
        rw [this]; exact ha
    rw [eset, ← Measure.map_apply (measurable_const_mul _) hB, hνi g g.2]
  · rw [he.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hνc)

theorem unique_sf (S : Subgroup G) (hS : IsClosed (S : Set G)) (μ m : Measure G) (hμ0 : μ ≠ 0)
    (hμc : μ (S : Set G)ᶜ = 0) (hμi : ∀ s ∈ S, μ.map (fun x => s * x) = μ) (hμf : IsFiniteMeasureOnCompacts μ)
    (hm0 : m ≠ 0) (hmσ : SigmaFinite m) (hmc : m (S : Set G)ᶜ = 0) (hmi : ∀ s ∈ S, m.map (fun x => s * x) = m) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ = c • m := by
  haveI : LocallyCompactSpace S := hS.locallyCompactSpace
  haveI : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology (S : Set G)
  have he : MeasurableEmbedding (Subtype.val : S → G) := MeasurableEmbedding.subtype_coe hS.measurableSet
  obtain ⟨hμ1, hμ3⟩ := comap_inv S hS μ hμc hμi
  obtain ⟨hm1, hm3⟩ := comap_inv S hS m hmc hmi
  set μ' := μ.comap (Subtype.val : S → G) with hμ'd
  set m' := m.comap (Subtype.val : S → G) with hm'd
  have : IsFiniteMeasureOnCompacts μ' := ⟨fun K hK => by
    rw [hμ'd, he.comap_apply]
    exact (hK.image continuous_subtype_val).measure_lt_top⟩
  haveI : SigmaFinite μ' := inferInstance
  haveI : SigmaFinite m' := SigmaFinite.of_map m' he.measurable.aemeasurable (by rw [hm3]; exact hmσ)
  haveI := hμ1
  haveI := hm1
  have hμ'0 : μ' ≠ 0 := fun h => hμ0 (by rw [← hμ3, h, Measure.map_zero])
  have hm'0 : m' ≠ 0 := fun h => hm0 (by rw [← hm3, h, Measure.map_zero])
  obtain ⟨s, hs0, hsT⟩ : ∃ s : Set S, μ' s ≠ 0 ∧ μ' s ≠ ∞ := by
    by_contra hcon
    push Not at hcon
    apply hμ'0
    have h0 : ∀ n, μ' (spanningSets μ' n) = 0 := fun n => by
      by_contra h
      exact (measure_spanningSets_lt_top μ' n).ne (hcon _ h)
    rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets μ']
    exact measure_iUnion_null h0
  have key : ∀ t : Set S, m' s * μ' t = μ' s * m' t := fun t => measure_mul_measure_eq m' μ' s t hs0 hsT
  have hms0 : m' s ≠ 0 := by
    intro h
    apply hm'0
    ext t _
    have e := key t
    rw [h, zero_mul] at e
    have h2 := (mul_eq_zero.1 e.symm).resolve_left hs0
    simp [h2]
  have hmsT : m' s ≠ ∞ := by
    intro h
    apply hμ'0
    have h0 : ∀ n, μ' (spanningSets m' n) = 0 := fun n => by
      have e := key (spanningSets m' n)
      rw [h] at e
      have hf : μ' s * m' (spanningSets m' n) ≠ ∞ :=
        ENNReal.mul_ne_top hsT (measure_spanningSets_lt_top m' n).ne
      rw [← e] at hf
      by_contra h0
      exact hf (ENNReal.top_mul h0)
    rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets m']
    exact measure_iUnion_null h0
  have hμ'eq : μ' = (μ' s / m' s) • m' := by
    ext t _
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.div_eq_inv_mul, mul_assoc, ← key t, ← mul_assoc,
      ENNReal.inv_mul_cancel hms0 hmsT, one_mul]
  have hfin : μ = (μ' s / m' s) • m := by
    conv_lhs => rw [← hμ3, hμ'eq]
    rw [Measure.map_smul, hm3]
  exact ⟨μ' s / m' s, (ENNReal.div_pos_iff.2 ⟨hs0, hmsT⟩).ne', ENNReal.div_ne_top hsT hms0, hfin⟩

end Gen

section SL

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S

variable {n r : ℕ}

theorem spanLt_pres (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) (hg : InS e z g)
    (a : ℕ) : ∀ y ∈ spanLt e a, g *ᵥ y ∈ spanLt e a := by
  intro y hy
  have hle : spanLt e a ≤ (spanLt e a).comap (Matrix.mulVecLin g) := by
    unfold spanLt
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    have hb' : (b : ℕ) < a := hb
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
    have e1 : g *ᵥ e b = e b + (g - 1) *ᵥ e b := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [e1]
    refine Submodule.add_mem _ (Submodule.subset_span ⟨b, hb', rfl⟩) ?_
    refine Submodule.span_mono ?_ (hg.1 b)
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, lt_trans hc hb', rfl⟩
  exact hle hy

theorem inS_mul (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) {g h : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g)
    (hh : InS e z h) : InS e z (g * h) := by
  have key : ∀ y : Fin n → ℂ, (g * h - 1) *ᵥ y = g *ᵥ ((h - 1) *ᵥ y) + (g - 1) *ᵥ y := fun y => by
    simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.one_mulVec, Matrix.mulVec_mulVec]
    abel
  refine ⟨fun a => ?_, ?_⟩
  · rw [key]; exact Submodule.add_mem _ (spanLt_pres e z g hg a.1 _ (hh.1 a)) (hg.1 a)
  · rw [key]; exact Submodule.add_mem _ (spanLt_pres e z g hg r _ hh.2) hg.2

theorem inS_one (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : InS e z (1 : Matrix (Fin n) (Fin n) ℂ) :=
  ⟨fun a => by simp, by simp⟩

theorem isClosed_sLoc (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : IsClosed (SLoc ε e z) := by
  have hc : Continuous (fun g : Formalism.REAL.UJ ε => uMat g) := (Formalism.REAL.uJEmb n ε).1.continuous
  have hcl : ∀ (W : Submodule ℂ (Fin n → ℂ)) (v : Fin n → ℂ),
      IsClosed {g : Formalism.REAL.UJ ε | (uMat g - 1) *ᵥ v ∈ W} := by
    intro W v
    have h1 : Continuous fun g : Formalism.REAL.UJ ε => (uMat g - 1) *ᵥ v :=
      Continuous.matrix_mulVec (hc.sub continuous_const) continuous_const
    exact IsClosed.preimage h1 (Submodule.closed_of_finiteDimensional W)
  have hset : SLoc ε e z = (⋂ a : Fin r, {g : Formalism.REAL.UJ ε | (uMat g - 1) *ᵥ e a ∈ spanLt e a.1}) ∩
      {g | (uMat g - 1) *ᵥ z ∈ spanLt e r} := by
    ext g
    constructor
    · intro hg
      obtain ⟨h1, h2⟩ := hg
      exact ⟨Set.mem_iInter.2 h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Set.mem_iInter.1 h1, h2⟩
  rw [hset]
  exact (isClosed_iInter fun a => hcl _ _).inter (hcl _ _)

theorem sLoc_clSub (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : IsClSub (SLoc ε e z) where
  one_mem := by
    show InS e z (uMat (1 : Formalism.REAL.UJ ε))
    have : uMat (1 : Formalism.REAL.UJ ε) = 1 := by simp [uMat]
    rw [this]; exact inS_one e z
  mul_mem := by
    intro x hx y hy
    show InS e z (uMat (x * y))
    have : uMat (x * y) = uMat x * uMat y := by simp [uMat]
    rw [this]; exact inS_mul e z hx hy
  inv_mem := by
    intro x hx
    exact Formalism.L2.SG.RealObj.InfCut.inS_inv e z (uMat x) (uMat x⁻¹) (Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' x) hx
  closed := isClosed_sLoc ε e z

end SL

section Main

variable {k r : ℕ}

theorem isUnit_det_of (ε : Fin (2 * r + k + 1) → Bool) (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hH : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r) : IsUnit P.det := by
  have h1 : (Formalism.QuantumDeterminants.Hpk k r).det ≠ 0 := by
    have h := congrArg Matrix.det (Formalism.QuantumDeterminants.hpkFacts k r).2.1
    rw [Matrix.det_mul, Matrix.det_one] at h
    intro h0
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  rw [isUnit_iff_ne_zero]
  intro h0
  apply h1
  rw [← hH, Matrix.det_mul, h0, mul_zero]

theorem psiP_eq (ε : Fin (2 * r + k + 1) → Bool) (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    psiP (ε := ε) P = Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P := rfl

theorem haarG (ε : Fin (2 * r + k + 1) → Bool) (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hH : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r) :
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) ((Formalism.REAL.muG ε).map (psiP P)) := by
  have hP := isUnit_det_of ε P hH
  have h := Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.haar_map (ε := ε) Formalism.REAL.uJEmb Formalism.REAL.unimodular Formalism.QuantumDeterminants.uHConj hP hH
  rw [psiP_eq]
  haveI : IsFiniteMeasureOnCompacts ((Formalism.REAL.muG ε).map (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P)) := ⟨h.finite_compact⟩
  exact ⟨inferInstance, h.ne_zero, h.conc, h.left⟩

end Main

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HC

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open HC

theorem haarCorr_of (hSC : SetCorr) : HaarCorr := by
  intro r k ε e z zH P hH hP he hzH hz hT _hk
  refine ⟨haarG ε P hH, ?_⟩
  intro μW μN hW hN μS hS
  have hSS := Formalism.MainNotions.BridgeCSB.haarS hzH hW hN
  have eS : Formalism.MainNotions.S.muS μW μN = (μW.prod μN).map Formalism.MainNotions.BridgeCSB.mulP := rfl
  rw [← eS] at hSS
  rw [psiP_eq]
  set ν := Formalism.MainNotions.S.muS μW μN with hνd
  set φ := Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P with hφd
  have hce : Topology.IsClosedEmbedding φ := Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi_closedEmbedding Formalism.REAL.uJEmb hP
  have hme : MeasurableEmbedding φ := hce.measurableEmbedding
  have hcorr : ∀ u : Formalism.REAL.UJ ε, u ∈ SLoc ε e z ↔ Matrix.of (φ u) ∈ Formalism.QuantumDeterminants.Sset k r zH :=
    fun u => hSC r k ε e z zH P hH hP he hzH hz hT u
  have hSsub : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x ∈ Formalism.QuantumDeterminants.Sset k r zH → x ∈ Set.range φ := fun x hx =>
    (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi_range_iff Formalism.REAL.uJEmb Formalism.QuantumDeterminants.uHConj hP hH x).2 (Formalism.QuantumDeterminants.Sset_UH hx)
  have hνc : ν (Set.range φ)ᶜ = 0 := measure_mono_null (fun x hx hS' => hx (hSsub x hS')) hSS.2.2.1
  have hmap : (ν.comap φ).map φ = ν := by
    rw [hme.map_comap]
    exact Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hνc)
  have hmσ : SigmaFinite (ν.comap φ) :=
    SigmaFinite.of_map _ hme.measurable.aemeasurable (by rw [hmap]; exact hSS.1)
  have hm0 : ν.comap φ ≠ 0 := fun h => hSS.2.1 (by rw [← hmap, h, Measure.map_zero])
  have hmc : (ν.comap φ) (SLoc ε e z)ᶜ = 0 := by
    rw [hme.comap_apply]
    refine measure_mono_null ?_ hSS.2.2.1
    rintro _ ⟨u, hu, rfl⟩ hS'
    exact hu ((hcorr u).2 hS')
  have hmi : ∀ u ∈ SLoc ε e z, (ν.comap φ).map (fun x => u * x) = ν.comap φ := by
    intro u hu
    ext A hA
    rw [Measure.map_apply (measurable_const_mul u) hA, hme.comap_apply, hme.comap_apply]
    have h1 := hSS.2.2.2 _ ((hcorr u).1 hu)
    have hs' : MeasurableSet (φ '' A) := hme.measurableSet_image.2 hA
    conv_rhs => rw [← h1, Measure.map_apply (Formalism.MainNotions.BridgeCSB.continuous_lmulM _).measurable hs']
    congr 1
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨u * w, hw, (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.lmul_phi hP u w).symm⟩
    · rintro ⟨v, hv, hx⟩
      refine ⟨u⁻¹ * v, by simpa using hv, ?_⟩
      have h2 : Formalism.QuantumDeterminants.lmulM (φ u⁻¹) (Formalism.QuantumDeterminants.lmulM (φ u) x) = x := by
        have h3 : (Matrix.of (φ u⁻¹) : Formalism.FourierDecayAlt.B.Mat k r) * Matrix.of (φ u) = 1 := by
          have := Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.lmul_phi hP u⁻¹ u
          rw [inv_mul_cancel] at this
          refine Eq.trans this ?_
          show P⁻¹ * (1 : Formalism.FourierDecayAlt.B.Mat k r) * P = 1
          rw [Matrix.mul_one, Matrix.nonsing_inv_mul P hP]
        show (Matrix.of (φ u⁻¹) : Formalism.FourierDecayAlt.B.Mat k r) * (Matrix.of (φ u) * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
      calc φ (u⁻¹ * v) = Formalism.QuantumDeterminants.lmulM (φ u⁻¹) (φ v) := (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.lmul_phi hP u⁻¹ v).symm
        _ = x := by rw [hx]; exact h2
  have hcl := sLoc_clSub ε e z
  have hSg : IsClosed ((HaarCore.subOf _ hcl.one_mem hcl.mul_mem hcl.inv_mem : Subgroup (Formalism.REAL.UJ ε)) :
      Set (Formalism.REAL.UJ ε)) := hcl.closed
  obtain ⟨c, hc0, hcT, hμS⟩ :=
    unique_sf _ hSg μS (ν.comap φ) hS.1.2.1 hS.1.2.2.1 hS.1.2.2.2 hS.2 hm0 hmσ hmc hmi
  refine ⟨c.toReal, ENNReal.toReal_pos hc0 hcT, ?_⟩
  rw [ENNReal.ofReal_toReal hcT, hμS, Measure.map_smul, hmap]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
