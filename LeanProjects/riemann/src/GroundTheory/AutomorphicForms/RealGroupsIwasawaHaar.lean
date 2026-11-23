import Mathlib
import GroundTheory.AutomorphicForms.RealGroupsIwasawa
import GroundTheory.AutomorphicForms.RealGroupsHaar

namespace GroundTheory.Automorphic

open Matrix Set
open scoped ComplexOrder

set_option linter.unusedSectionVars false

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n]

theorem rclike_inv_pos {z : 𝕜} (hz : 0 < z) : 0 < z⁻¹ := by
  obtain ⟨hre, him⟩ := RCLike.pos_iff.1 hz
  have hz' : z = (RCLike.re z : 𝕜) := by rw [← RCLike.re_add_im z, him]; simp
  rw [hz', ← RCLike.ofReal_inv]
  exact RCLike.ofReal_pos.2 (inv_pos.2 hre)

def upperPosSubgroup (n 𝕜 : Type*) [RCLike 𝕜] [Fintype n] [LinearOrder n] : Subgroup (GL n 𝕜) where
  carrier := {g | (g : Matrix n n 𝕜).IsUpperTriangular ∧ ∀ i, 0 < (g : Matrix n n 𝕜) i i}
  mul_mem' {a b} ha hb := ⟨ha.1.mul hb.1, fun i => by
    rw [Units.val_mul, mul_apply_self_of_isUpperTriangular ha.1 hb.1]
    exact mul_pos (ha.2 i) (hb.2 i)⟩
  one_mem' := ⟨blockTriangular_one, fun i => by simp⟩
  inv_mem' {a} ha := by
    let : Invertible (a : Matrix n n 𝕜) :=
      invertibleOfIsUnitDet _ ((isUnit_iff_isUnit_det _).1 a.isUnit)
    have hinv : ((a⁻¹ : GL n 𝕜) : Matrix n n 𝕜) = (a : Matrix n n 𝕜)⁻¹ := coe_units_inv a
    have hU : ((a⁻¹ : GL n 𝕜) : Matrix n n 𝕜).IsUpperTriangular := by
      rw [hinv]; exact blockTriangular_inv_of_blockTriangular ha.1
    refine ⟨hU, fun i => ?_⟩
    have e0 : ((a⁻¹ : GL n 𝕜) : Matrix n n 𝕜) * (a : Matrix n n 𝕜) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e := congrFun (congrFun e0 i) i
    rw [mul_apply_self_of_isUpperTriangular hU ha.1, one_apply_eq] at e
    rw [eq_inv_of_mul_eq_one_left e]
    exact rclike_inv_pos (ha.2 i)

theorem mem_upperPosSubgroup {g : GL n 𝕜} :
    g ∈ upperPosSubgroup n 𝕜 ↔
      (g : Matrix n n 𝕜).IsUpperTriangular ∧ ∀ i, 0 < (g : Matrix n n 𝕜) i i := Iff.rfl

def kbMul (p : unitaryGroup n 𝕜 × upperPosSubgroup n 𝕜) : GL n 𝕜 :=
  Unitary.toUnits p.1 * p.2

section Split

variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

theorem conjTranspose_iwasawaK_mul_mem (g : GL n 𝕜) :
    (Unitary.toUnits (iwasawaK g))⁻¹ * g ∈ upperPosSubgroup n 𝕜 := by
  have e : (((Unitary.toUnits (iwasawaK g))⁻¹ * g : GL n 𝕜) : Matrix n n 𝕜) =
      ((iwasawaK g : Matrix n n 𝕜))ᴴ * g := rfl
  rw [mem_upperPosSubgroup, e, iwasawaK_conjTranspose_mul]
  refine ⟨(blockTriangular_diagonal _).mul (iwasawaEquiv.symm g).2.2.2.1, fun i => ?_⟩
  rw [diagonal_mul, (iwasawaEquiv.symm g).2.2.2.2 i, mul_one]
  exact RCLike.ofReal_pos.2 ((iwasawaEquiv.symm g).2.1.2 i)

noncomputable def kbSplit (g : GL n 𝕜) : unitaryGroup n 𝕜 × upperPosSubgroup n 𝕜 :=
  (iwasawaK g, ⟨_, conjTranspose_iwasawaK_mul_mem g⟩)

theorem iwasawaK_kbMul (p : unitaryGroup n 𝕜 × upperPosSubgroup n 𝕜) :
    iwasawaK (kbMul p) = p.1 := by
  symm
  apply eq_iwasawaK_of_mem
  have e : ((p.1 : Matrix n n 𝕜))ᴴ * (kbMul p : Matrix n n 𝕜) = ((p.2 : GL n 𝕜) : Matrix n n 𝕜) := by
    show ((p.1 : Matrix n n 𝕜))ᴴ * ((p.1 : Matrix n n 𝕜) * ((p.2 : GL n 𝕜) : Matrix n n 𝕜)) = _
    rw [← Matrix.mul_assoc, show ((p.1 : Matrix n n 𝕜))ᴴ * p.1 = 1 from p.1.2.1, Matrix.one_mul]
  refine ⟨?_, fun i => ?_⟩
  · rw [e]; exact p.2.2.1
  · rw [e]
    obtain ⟨hre, him⟩ := RCLike.pos_iff.1 (p.2.2.2 i)
    exact ⟨hre.le, him⟩

noncomputable def kbHomeomorph : unitaryGroup n 𝕜 × upperPosSubgroup n 𝕜 ≃ₜ GL n 𝕜 where
  toFun := kbMul
  invFun := kbSplit
  left_inv p := by
    ext : 1
    · exact iwasawaK_kbMul p
    · apply Subtype.ext
      show (Unitary.toUnits (iwasawaK (kbMul p)))⁻¹ * (Unitary.toUnits p.1 * p.2) = p.2
      rw [iwasawaK_kbMul, inv_mul_cancel_left]
  right_inv g := by
    show Unitary.toUnits (iwasawaK g) * ((Unitary.toUnits (iwasawaK g))⁻¹ * g) = g
    rw [mul_inv_cancel_left]
  continuous_toFun := by
    have ht : Continuous (fun k : unitaryGroup n 𝕜 => Unitary.toUnits k) :=
      Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.star⟩
    exact (ht.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    have ht : Continuous (fun k : unitaryGroup n 𝕜 => Unitary.toUnits k) :=
      Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.star⟩
    refine continuous_iwasawaK.prodMk (Continuous.subtype_mk ?_ _)
    exact ((ht.comp continuous_iwasawaK).inv).mul continuous_id

theorem kbHomeomorph_apply (p : unitaryGroup n 𝕜 × upperPosSubgroup n 𝕜) :
    kbHomeomorph p = Unitary.toUnits p.1 * p.2 := rfl

end Split

section HaarKB

open MeasureTheory Measure
open scoped ENNReal NNReal Matrix.Norms.L2Operator

instance : SecondCountableTopology (Matrix n n ℝ) :=
  inferInstanceAs (SecondCountableTopology (n → n → ℝ))

instance : SecondCountableTopology (GL n ℝ) :=
  (Units.isOpenEmbedding_val (R := Matrix n n ℝ)).isEmbedding.secondCountableTopology

instance : LocallyCompactSpace (GL n ℝ) :=
  (Units.isOpenEmbedding_val (R := Matrix n n ℝ)).locallyCompactSpace

instance : SecondCountableTopology (upperPosSubgroup n ℝ) :=
  TopologicalSpace.Subtype.secondCountableTopology _

variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

theorem isClosed_upperPosSubgroup : IsClosed (upperPosSubgroup n ℝ : Set (GL n ℝ)) := by
  have e : (upperPosSubgroup n ℝ : Set (GL n ℝ)) =
      (⋂ i, ⋂ j, {g : GL n ℝ | j < i → (g : Matrix n n ℝ) i j = 0}) ∩
        ⋂ i, {g : GL n ℝ | 0 ≤ (g : Matrix n n ℝ) i i} := by
    ext g
    simp only [SetLike.mem_coe, mem_upperPosSubgroup, mem_inter_iff, mem_iInter, mem_ofPred_eq]
    constructor
    · rintro ⟨hU, hpos⟩; exact ⟨fun i j h => hU h, fun i => (hpos i).le⟩
    · rintro ⟨hU, hnn⟩
      have hU' : (g : Matrix n n ℝ).IsUpperTriangular := fun i j h => hU i j h
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

instance : LocallyCompactSpace (upperPosSubgroup n ℝ) :=
  isClosed_upperPosSubgroup.locallyCompactSpace

noncomputable def kbInvHomeomorph : GL n ℝ ≃ₜ unitaryGroup n ℝ × upperPosSubgroup n ℝ :=
  kbHomeomorph.symm.trans ((Homeomorph.refl _).prodCongr (Homeomorph.inv _))

theorem kbInvHomeomorph_equivariant (q : unitaryGroup n ℝ × upperPosSubgroup n ℝ) (g : GL n ℝ) :
    kbInvHomeomorph (Unitary.toUnits q.1 * g * ((q.2 : GL n ℝ))⁻¹) = q * kbInvHomeomorph g := by
  obtain ⟨p, rfl⟩ := kbHomeomorph.surjective g
  have e : Unitary.toUnits q.1 * kbHomeomorph p * ((q.2 : GL n ℝ))⁻¹ =
      kbHomeomorph (q.1 * p.1, p.2 * q.2⁻¹) := by
    simp only [kbHomeomorph_apply, map_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
  rw [e]
  simp only [kbInvHomeomorph, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  refine Prod.ext rfl ?_
  show (p.2 * q.2⁻¹)⁻¹ = q.2 * p.2⁻¹
  rw [_root_.mul_inv_rev, inv_inv]

theorem haarGLReal_eq_smul_map_kbHomeomorph (μ₀ : Measure (Matrix n n ℝ)) [μ₀.IsAddHaarMeasure]
    (μK : Measure (unitaryGroup n ℝ)) [μK.IsHaarMeasure]
    (μB : Measure (upperPosSubgroup n ℝ)) [μB.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧
      haarGLReal μ₀ = c • Measure.map kbHomeomorph (μK.prod μB.inv) := by
  set H := haarGLReal μ₀ with hHdef
  set f := kbInvHomeomorph (n := n)
  set ν := Measure.map f H with hνdef
  have hν : ν.IsMulLeftInvariant := ⟨fun q => by
    rw [hνdef, Measure.map_map (measurable_const_mul q) f.measurable]
    have e1 : (fun x => q * x) ∘ f =
        f ∘ (fun g => Unitary.toUnits q.1 * g * ((q.2 : GL n ℝ))⁻¹) :=
      funext fun g => (kbInvHomeomorph_equivariant q g).symm
    have e2 : (fun g : GL n ℝ => Unitary.toUnits q.1 * g * ((q.2 : GL n ℝ))⁻¹) =
        (fun g => g * ((q.2 : GL n ℝ))⁻¹) ∘ (fun g => Unitary.toUnits q.1 * g) := rfl
    have hmT : Measurable (fun g : GL n ℝ => Unitary.toUnits q.1 * g * ((q.2 : GL n ℝ))⁻¹) := by
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
    have e3 : ⇑f.symm = kbHomeomorph ∘ Prod.map id (fun b : upperPosSubgroup n ℝ => b⁻¹) := by
      funext p; rfl
    rw [e3, ← Measure.map_map kbHomeomorph.measurable (measurable_id.prodMap measurable_inv),
      ← Measure.map_prod_map _ _ measurable_id measurable_inv, Measure.map_id, Measure.inv_def]

theorem lintegral_haarGLReal_iwasawa (μ₀ : Measure (Matrix n n ℝ)) [μ₀.IsAddHaarMeasure]
    (μK : Measure (unitaryGroup n ℝ)) [μK.IsHaarMeasure]
    (μB : Measure (upperPosSubgroup n ℝ)) [μB.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL n ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂(haarGLReal μ₀) =
        c * ∫⁻ k, ∫⁻ b, f (Unitary.toUnits k * b) ∂μB.inv ∂μK := by
  obtain ⟨c, hc, h⟩ := haarGLReal_eq_smul_map_kbHomeomorph μ₀ μK μB
  refine ⟨c, hc, fun f hf => ?_⟩
  rw [h, lintegral_smul_measure, lintegral_map hf kbHomeomorph.measurable]
  have := lintegral_prod (μ := μK) (ν := μB.inv) _ (hf.comp kbHomeomorph.measurable).aemeasurable
  simp only [Function.comp_def] at this
  rw [this, ENNReal.smul_def, smul_eq_mul]
  rfl

end HaarKB

end GroundTheory.Automorphic
