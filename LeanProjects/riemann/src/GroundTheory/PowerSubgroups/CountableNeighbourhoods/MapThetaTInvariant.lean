import Mathlib
import GroundTheory.AutomorphicForms.ContragredientTranspose.GelfandKazhdan

namespace GroundTheory.Variant₂.N1

open MeasureTheory Topology Filter ValuativeRel

namespace MapThetaTInvariant

section LocalField

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

lemma countable_valueGroupWithZero : Countable (ValueGroupWithZero F) :=
  haveI : Countable (WithZero (Multiplicative ℤ)) := inferInstanceAs (Countable (Option ℤ))
  Countable.of_equiv _ (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).toEquiv.symm

lemma nhds_zero_isCountablyGenerated : (𝓝 (0 : F)).IsCountablyGenerated := by
  have := countable_valueGroupWithZero F
  exact (IsValuativeTopology.hasBasis_nhds_zero' F).isCountablyGenerated

lemma sigmaCompactSpace : SigmaCompactSpace F := by
  have := countable_valueGroupWithZero F
  refine SigmaCompactSpace.of_countable
    (Set.range fun γ : ValueGroupWithZero F => {x : F | valuation F x ≤ γ})
    (Set.countable_range _) ?_ ?_
  · rintro _ ⟨γ, rfl⟩
    exact IsNonarchimedeanLocalField.isCompact_closedBall F γ
  · ext x
    simp only [Set.sUnion_range, Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨_, le_rfl⟩

lemma metrizableSpace : TopologicalSpace.MetrizableSpace F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  have := nhds_zero_isCountablyGenerated F
  have := IsUniformAddGroup.uniformity_countably_generated (α := F)
  exact UniformSpace.metrizableSpace

lemma secondCountableTopology : SecondCountableTopology F := by
  have := sigmaCompactSpace F
  have := metrizableSpace F
  infer_instance

end LocalField

section GeneralLinear

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

lemma secondCountableTopology_GL : SecondCountableTopology (GL (Fin n) F) := by
  have := secondCountableTopology F
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → F))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) F)).symm.isEmbedding.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

open GroundTheory.Automorphic.ContragredientTranspose in

lemma continuous_transposeGL {F : Type*} [Field F] [TopologicalSpace F] {n : ℕ} :
    Continuous (transposeGL : GL (Fin n) F → GL (Fin n) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_transpose
  · exact Units.continuous_coe_inv.matrix_transpose

open GroundTheory.Automorphic.ContragredientTranspose in

noncomputable def thetaTContinuous : GL (Fin n) F ≃ₜ* GL (Fin n) F :=
  { (thetaT : GL (Fin n) F ≃* GL (Fin n) F) with
    continuous_toFun := continuous_transposeGL.inv
    continuous_invFun := continuous_transposeGL.inv }

open GroundTheory.Automorphic.ContragredientTranspose in

lemma thetaT_thetaT {F : Type*} [Field F] {n : ℕ} (g : GL (Fin n) F) :
    (thetaT : GL (Fin n) F ≃* GL (Fin n) F) (thetaT g) = g :=
  (thetaT : GL (Fin n) F ≃* GL (Fin n) F).symm_apply_apply g

end GeneralLinear

end MapThetaTInvariant

open MapThetaTInvariant

open GroundTheory.Automorphic.ContragredientTranspose in

theorem map_thetaT_eq_self {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {n : ℕ} [MeasurableSpace (GL (Fin n) F)]
    [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    Measure.map (⇑thetaT) μ = μ := by
  have := secondCountableTopology_GL (F := F) (n := n)
  set θ : GL (Fin n) F ≃ₜ* GL (Fin n) F := thetaTContinuous
  have hθ : ⇑(thetaT : GL (Fin n) F ≃* GL (Fin n) F) = ⇑θ := rfl
  have hmeas : Measurable θ := θ.continuous.measurable
  rw [hθ]
  have hc := Measure.isMulLeftInvariant_eq_smul (μ.map θ) μ
  set c := Measure.haarScalarFactor (μ.map θ) μ

  have h2 : (μ.map θ).map θ = μ := by
    rw [Measure.map_map hmeas hmeas]
    convert Measure.map_id
    ext g : 1
    exact thetaT_thetaT g
  have hsq : (c * c) • μ = μ := by
    conv_rhs => rw [← h2, hc, Measure.map_smul, hc, smul_smul]

  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : GL (Fin n) F)
  have hpos : 0 < μ K := Measure.measure_pos_of_mem_nhds μ hK1
  have hfin : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have hcc : c * c = 1 := by
    have := congrArg (fun ν : Measure (GL (Fin n) F) => ν K) hsq
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
    have h' : ((c * c : NNReal) : ENNReal) * μ K = 1 * μ K := by rw [one_mul]; exact this
    have := (ENNReal.mul_left_inj hpos.ne' hfin).1 h'
    exact_mod_cast this
  have hc1 : c = 1 := by
    have h0 : (0 : NNReal) ≤ c := c.2
    nlinarith [mul_self_nonneg (c - 1)]
  rw [hc, hc1, one_smul]

end GroundTheory.Variant₂.N1
