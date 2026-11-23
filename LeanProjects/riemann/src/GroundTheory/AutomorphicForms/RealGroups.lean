import Mathlib
import GroundTheory.AutomorphicForms.RealGroupsLie
import GroundTheory.AutomorphicForms.RealGroupsPolar
import GroundTheory.AutomorphicForms.RealGroupsKAK
import GroundTheory.AutomorphicForms.RealGroupsIwasawa
import GroundTheory.AutomorphicForms.RealGroupsHaar
import GroundTheory.AutomorphicForms.RealGroupsIwasawaHaar

namespace GroundTheory.Automorphic

open Matrix Set
open scoped ComplexOrder

set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [LinearOrder n]

section HaarKBComplex

open MeasureTheory Measure
open scoped ENNReal NNReal Matrix.Norms.L2Operator

instance : SecondCountableTopology (Matrix n n ℂ) :=
  inferInstanceAs (SecondCountableTopology (n → n → ℂ))

instance : SecondCountableTopology (GL n ℂ) :=
  (Units.isOpenEmbedding_val (R := Matrix n n ℂ)).isEmbedding.secondCountableTopology

instance : LocallyCompactSpace (GL n ℂ) :=
  (Units.isOpenEmbedding_val (R := Matrix n n ℂ)).locallyCompactSpace

instance : SecondCountableTopology (upperPosSubgroup n ℂ) :=
  TopologicalSpace.Subtype.secondCountableTopology _

variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

theorem isClosed_upperPosSubgroupC : IsClosed (upperPosSubgroup n ℂ : Set (GL n ℂ)) := by
  have e : (upperPosSubgroup n ℂ : Set (GL n ℂ)) =
      (⋂ i, ⋂ j, {g : GL n ℂ | j < i → (g : Matrix n n ℂ) i j = 0}) ∩
        ⋂ i, {g : GL n ℂ | 0 ≤ (g : Matrix n n ℂ) i i} := by
    ext g
    simp only [SetLike.mem_coe, mem_upperPosSubgroup, mem_inter_iff, mem_iInter, mem_ofPred_eq]
    constructor
    · rintro ⟨hU, hpos⟩; exact ⟨fun i j h => hU h, fun i => (hpos i).le⟩
    · rintro ⟨hU, hnn⟩
      have hU' : (g : Matrix n n ℂ).IsUpperTriangular := fun i j h => hU i j h
      refine ⟨hU', fun i => lt_of_le_of_ne (hnn i) (Ne.symm ?_)⟩
      have hdet := ((isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
      rw [det_of_isUpperTriangular hU'] at hdet
      exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ i)
  rw [e]
  refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
    (isClosed_iInter fun i => ?_)
  · by_cases h : j < i
    · simp only [h, forall_const]
      exact isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const
    · simp only [h, IsEmpty.forall_iff, ofPred_true, isClosed_univ]
  · exact isClosed_le continuous_const (Units.continuous_val.matrix_elem i i)

instance : LocallyCompactSpace (upperPosSubgroup n ℂ) :=
  isClosed_upperPosSubgroupC.locallyCompactSpace

noncomputable def kbInvHomeomorphC : GL n ℂ ≃ₜ unitaryGroup n ℂ × upperPosSubgroup n ℂ :=
  kbHomeomorph.symm.trans ((Homeomorph.refl _).prodCongr (Homeomorph.inv _))

theorem kbInvHomeomorphC_equivariant (q : unitaryGroup n ℂ × upperPosSubgroup n ℂ) (g : GL n ℂ) :
    kbInvHomeomorphC (Unitary.toUnits q.1 * g * ((q.2 : GL n ℂ))⁻¹) = q * kbInvHomeomorphC g := by
  obtain ⟨p, rfl⟩ := kbHomeomorph.surjective g
  have e : Unitary.toUnits q.1 * kbHomeomorph p * ((q.2 : GL n ℂ))⁻¹ =
      kbHomeomorph (q.1 * p.1, p.2 * q.2⁻¹) := by
    simp only [kbHomeomorph_apply, map_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
  rw [e]
  simp only [kbInvHomeomorphC, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  refine Prod.ext rfl ?_
  show (p.2 * q.2⁻¹)⁻¹ = q.2 * p.2⁻¹
  rw [_root_.mul_inv_rev, inv_inv]

theorem haarGLComplex_eq_smul_map_kbHomeomorph (μ₀ : Measure (Matrix n n ℂ)) [μ₀.IsAddHaarMeasure]
    (μK : Measure (unitaryGroup n ℂ)) [μK.IsHaarMeasure]
    (μB : Measure (upperPosSubgroup n ℂ)) [μB.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧
      haarGLComplex μ₀ = c • Measure.map kbHomeomorph (μK.prod μB.inv) := by
  set H := haarGLComplex μ₀ with hHdef
  set f := kbInvHomeomorphC (n := n)
  set ν := Measure.map f H with hνdef
  have hν : ν.IsMulLeftInvariant := ⟨fun q => by
    rw [hνdef, Measure.map_map (measurable_const_mul q) f.measurable]
    have e1 : (fun x => q * x) ∘ f =
        f ∘ (fun g => Unitary.toUnits q.1 * g * ((q.2 : GL n ℂ))⁻¹) :=
      funext fun g => (kbInvHomeomorphC_equivariant q g).symm
    have e2 : (fun g : GL n ℂ => Unitary.toUnits q.1 * g * ((q.2 : GL n ℂ))⁻¹) =
        (fun g => g * ((q.2 : GL n ℂ))⁻¹) ∘ (fun g => Unitary.toUnits q.1 * g) := rfl
    have hmT : Measurable (fun g : GL n ℂ => Unitary.toUnits q.1 * g * ((q.2 : GL n ℂ))⁻¹) := by
      rw [e2]; exact (measurable_mul_const _).comp (measurable_const_mul _)
    rw [e1, ← Measure.map_map f.measurable hmT, e2,
      ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _), map_mul_left_eq_self,
      map_mul_right_eq_self]⟩
  have hνc : IsFiniteMeasureOnCompacts ν := IsFiniteMeasureOnCompacts.map H f
  obtain ⟨c, key⟩ : ∃ c : ℝ≥0, ν = c • μK.prod μB :=
    ⟨_, isMulLeftInvariant_eq_smul ν (μK.prod μB)⟩
  have hH : H = Measure.map f.symm ν := by
    rw [hνdef, Measure.map_map f.symm.measurable f.measurable]
    simp
  refine ⟨c, ?_, ?_⟩
  · intro hc
    rw [hc, zero_smul] at key
    have h0 : H Set.univ = 0 := by rw [hH, key, Measure.map_zero, Measure.coe_zero, Pi.zero_apply]
    exact (IsOpenPosMeasure.open_pos Set.univ isOpen_univ Set.univ_nonempty) h0
  · rw [hH, key, Measure.map_smul]
    congr 1
    have e3 : ⇑f.symm = kbHomeomorph ∘ Prod.map id (fun b : upperPosSubgroup n ℂ => b⁻¹) := by
      funext p; rfl
    rw [e3, ← Measure.map_map kbHomeomorph.measurable (measurable_id.prodMap measurable_inv),
      ← Measure.map_prod_map _ _ measurable_id measurable_inv, Measure.map_id, Measure.inv_def]

theorem lintegral_haarGLComplex_iwasawa (μ₀ : Measure (Matrix n n ℂ)) [μ₀.IsAddHaarMeasure]
    (μK : Measure (unitaryGroup n ℂ)) [μK.IsHaarMeasure]
    (μB : Measure (upperPosSubgroup n ℂ)) [μB.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL n ℂ → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂(haarGLComplex μ₀) =
        c * ∫⁻ k, ∫⁻ b, f (Unitary.toUnits k * b) ∂μB.inv ∂μK := by
  obtain ⟨c, hc, h⟩ := haarGLComplex_eq_smul_map_kbHomeomorph μ₀ μK μB
  refine ⟨c, hc, fun f hf => ?_⟩
  rw [h, lintegral_smul_measure, lintegral_map hf kbHomeomorph.measurable]
  have := lintegral_prod (μ := μK) (ν := μB.inv) _ (hf.comp kbHomeomorph.measurable).aemeasurable
  simp only [Function.comp_def] at this
  rw [this, ENNReal.smul_def, smul_eq_mul]
  rfl

end HaarKBComplex

end GroundTheory.Automorphic
