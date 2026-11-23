import Mathlib

noncomputable section

namespace PI.IwaMeasEx.MF

open MeasureTheory Measure Set
open scoped ENNReal NNReal

section Idx

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem measure_eq_relIndex_mul (μ : Measure G) [IsMulLeftInvariant μ] {U W : Subgroup G} (hWU : W ≤ U)
    (hU : MeasurableSet (U : Set G)) (hW : MeasurableSet (W : Set G)) (hfin : W.relIndex U ≠ 0) :
    μ U = W.relIndex U * μ W := by
  classical
  have hcard : Nat.card (U ⧸ W.subgroupOf U) = W.relIndex U := rfl
  haveI : Finite (U ⧸ W.subgroupOf U) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hfin)
  letI : Fintype (U ⧸ W.subgroupOf U) := Fintype.ofFinite _
  choose r hr using fun q : U ⧸ W.subgroupOf U => QuotientGroup.mk_surjective q
  have hC : (U : Set G) = ⋃ q, (fun x => ((r q : U) : G)⁻¹ * x) ⁻¹' (W : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · intro hx
      refine ⟨(QuotientGroup.mk (⟨x, hx⟩ : U) : U ⧸ W.subgroupOf U), ?_⟩
      have h := QuotientGroup.eq.mp (hr (QuotientGroup.mk (⟨x, hx⟩ : U)))
      rw [Subgroup.mem_subgroupOf] at h
      simpa using h
    · rintro ⟨q, hq⟩
      have e : x = ((r q : U) : G) * (((r q : U) : G)⁻¹ * x) := by group
      rw [e]
      exact U.mul_mem (r q).2 (hWU hq)
  have hdisj : Pairwise (Function.onFun Disjoint fun q => (fun x => ((r q : U) : G)⁻¹ * x) ⁻¹' (W : Set G)) := by
    intro q q' hne
    change Disjoint ((fun x => ((r q : U) : G)⁻¹ * x) ⁻¹' (W : Set G))
      ((fun x => ((r q' : U) : G)⁻¹ * x) ⁻¹' (W : Set G))
    refine Set.disjoint_left.mpr ?_
    intro x hx hx'
    apply hne
    simp only [Set.mem_preimage, SetLike.mem_coe] at hx hx'
    rw [← hr q, ← hr q']
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    have key : ((r q : U) : G)⁻¹ * ((r q' : U) : G) ∈ W := by
      have e : ((r q : U) : G)⁻¹ * ((r q' : U) : G) =
          (((r q : U) : G)⁻¹ * x) * (((r q' : U) : G)⁻¹ * x)⁻¹ := by group
      rw [e]
      exact W.mul_mem hx (W.inv_mem hx')
    simpa using key
  have hmeas : ∀ q, MeasurableSet ((fun x => ((r q : U) : G)⁻¹ * x) ⁻¹' (W : Set G)) :=
    fun q => hW.preimage (measurable_const_mul _)
  have hval : ∀ q, μ ((fun x => ((r q : U) : G)⁻¹ * x) ⁻¹' (W : Set G)) = μ W :=
    fun q => measure_preimage_mul μ _ _
  have hfc : (Fintype.card (U ⧸ W.subgroupOf U) : ℝ≥0∞) = (W.relIndex U : ℝ≥0∞) := by
    rw [← Nat.card_eq_fintype_card, hcard]
  rw [hC, measure_iUnion hdisj hmeas, tsum_fintype]
  simp only [hval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hfc]

end Idx

section Conj

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def conjSub (H : Subgroup G) (g : G) (hg : ∀ x, x ∈ H ↔ g * x * g⁻¹ ∈ H) : H ≃ₜ* H where
  toFun x := ⟨g * x * g⁻¹, (hg x).1 x.2⟩
  invFun x := ⟨g⁻¹ * x * g, (hg _).2 (by
    have e : g * (g⁻¹ * (x : G) * g) * g⁻¹ = x := by group
    rw [e]; exact x.2)⟩
  left_inv x := by ext; simp only; group
  right_inv x := by ext; simp only; group
  map_mul' x y := by ext; simp only [Subgroup.coe_mul]; group
  continuous_toFun := Continuous.subtype_mk
    ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  continuous_invFun := Continuous.subtype_mk
    ((continuous_const.mul continuous_subtype_val).mul continuous_const) _

end Conj

section Scale

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

theorem haar_map_eq_relIndex (φ : G ≃ₜ* G) (U : Subgroup G) (hUo : IsOpen (U : Set G))
    (hUc : IsCompact (U : Set G))
    (h1 : (U ⊓ U.comap φ.toMulEquiv.toMonoidHom).relIndex U ≠ 0)
    (h2 : (U ⊓ U.comap φ.toMulEquiv.toMonoidHom).relIndex (U.comap φ.toMulEquiv.toMonoidHom) ≠ 0) :
    (haar : Measure G).map φ = ENNReal.ofReal
      (((U ⊓ U.comap φ.toMulEquiv.toMonoidHom).relIndex (U.comap φ.toMulEquiv.toMonoidHom) : ℝ) /
        ((U ⊓ U.comap φ.toMulEquiv.toMonoidHom).relIndex U : ℝ)) • (haar : Measure G) := by
  classical
  have hφm : Measurable φ := φ.continuous.measurable
  have hW'set : ((U.comap φ.toMulEquiv.toMonoidHom : Subgroup G) : Set G) = φ ⁻¹' (U : Set G) := by
    first
      | rfl
      | (ext x; rfl)
      | (ext x; simp)
  have hUm : MeasurableSet (U : Set G) := hUo.measurableSet
  have hW'o : IsOpen ((U.comap φ.toMulEquiv.toMonoidHom : Subgroup G) : Set G) := by
    rw [hW'set]; exact hUo.preimage φ.continuous
  have hVo : IsOpen ((U ⊓ U.comap φ.toMulEquiv.toMonoidHom : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hUo.inter hW'o
  have eU := measure_eq_relIndex_mul (haar : Measure G) (U := U)
    (W := U ⊓ U.comap φ.toMulEquiv.toMonoidHom) inf_le_left hUm hVo.measurableSet h1
  have eW := measure_eq_relIndex_mul (haar : Measure G)
    (U := U.comap φ.toMulEquiv.toMonoidHom) (W := U ⊓ U.comap φ.toMulEquiv.toMonoidHom)
    inf_le_right hW'o.measurableSet hVo.measurableSet h2
  have hV0 : (haar : Measure G) ((U ⊓ U.comap φ.toMulEquiv.toMonoidHom : Subgroup G) : Set G) ≠ 0 :=
    hVo.measure_ne_zero _ ⟨1, Subgroup.one_mem _⟩
  have hVtop : (haar : Measure G) ((U ⊓ U.comap φ.toMulEquiv.toMonoidHom : Subgroup G) : Set G) ≠ ∞ :=
    ((measure_mono (SetLike.coe_subset_coe.mpr
      (inf_le_left : U ⊓ U.comap φ.toMulEquiv.toMonoidHom ≤ U))).trans_lt hUc.measure_lt_top).ne
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0∞, (haar : Measure G).map φ = c • (haar : Measure G) := by
    haveI hreg : Regular (haar : Measure G) := by
      first
        | infer_instance
        | exact regular_haarMeasure
    haveI : IsHaarMeasure ((haar : Measure G).map φ) := by
      first
        | infer_instance
        | exact ContinuousMulEquiv.isHaarMeasure_map (haar : Measure G) φ
        | exact φ.isHaarMeasure_map (haar : Measure G)
        | exact isHaarMeasure_map (haar : Measure G) φ.toMulEquiv.toMonoidHom φ.continuous
            φ.surjective φ.toHomeomorph.isClosedEmbedding.tendsto_cocompact
    haveI : Regular ((haar : Measure G).map φ) := by
      first
        | infer_instance
        | exact Regular.map (μ := (haar : Measure G)) φ.toHomeomorph
        | exact hreg.map φ.toHomeomorph
    first
      | exact ⟨_, (isMulLeftInvariant_eq_smul_of_regular ((haar : Measure G).map φ)
          (haar : Measure G)).trans (ENNReal.smul_def _ _)⟩
      | exact ⟨_, (isMulLeftInvariant_eq_smul_of_regular ((haar : Measure G).map φ)
          (haar : Measure G)).trans rfl⟩
      | exact ⟨_, haarMeasure_unique ((haar : Measure G).map φ) _⟩
      | exact ⟨_, (isMulLeftInvariant_eq_smul_of_regular ((haar : Measure G).map φ)
          (haar : Measure G)).trans (by ext s _; simp)⟩
  have hνU : (haar : Measure G).map φ (U : Set G) = (c • (haar : Measure G)) (U : Set G) := by
    rw [hc]
  rw [Measure.map_apply hφm hUm, ← hW'set, Measure.smul_apply, smul_eq_mul, eU, eW,
    ← mul_assoc] at hνU
  have hca : c * ((U ⊓ U.comap φ.toMulEquiv.toMonoidHom).relIndex U : ℝ≥0∞) =
      ((U ⊓ U.comap φ.toMulEquiv.toMonoidHom).relIndex (U.comap φ.toMulEquiv.toMonoidHom) : ℝ≥0∞) := by
    first
      | exact ((ENNReal.mul_eq_mul_right hV0 hVtop).mp hνU).symm
      | exact ((ENNReal.mul_left_inj hV0 hVtop).mp hνU).symm
      | (have h' := congrArg (· / (haar : Measure G)
            ((U ⊓ U.comap φ.toMulEquiv.toMonoidHom : Subgroup G) : Set G)) hνU
         simp only [ENNReal.mul_div_cancel_right hV0 hVtop] at h'
         exact h'.symm)
  rw [hc]
  congr 1
  rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h1)), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast, ENNReal.eq_div_iff (by exact_mod_cast h1) (by simp), mul_comm]
  exact hca

end Scale

end PI.IwaMeasEx.MF

end
