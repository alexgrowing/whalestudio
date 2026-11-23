import Mathlib
import GroundTheory.AutomorphicForms.MeasuresModulus

noncomputable section

open Matrix Module ValuativeRel MeasureTheory

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

theorem measure_eq_relIndex_mul' (G : Type) [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]
    (μ : MeasureTheory.Measure G) [μ.IsAddLeftInvariant] (H K : AddSubgroup G) (hHK : H ≤ K)
    (hH : MeasurableSet (H : Set G)) (hi : H.relIndex K ≠ 0) :
    μ (K : Set G) = (H.relIndex K : ENNReal) * μ (H : Set G) := by
  classical
  have hfi : (H.addSubgroupOf K).FiniteIndex := ⟨hi⟩
  haveI : Finite (K ⧸ H.addSubgroupOf K) := AddSubgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (K ⧸ H.addSubgroupOf K) := Fintype.ofFinite _
  let c : (K ⧸ H.addSubgroupOf K) → Set G :=
    fun q => (fun x => -((Quotient.out q : K) : G) + x) ⁻¹' (H : Set G)
  have hmem : ∀ q x, x ∈ c q ↔ -((Quotient.out q : K) : G) + x ∈ H := fun q x => Iff.rfl
  have hU : (K : Set G) = ⋃ q ∈ (Finset.univ : Finset (K ⧸ H.addSubgroupOf K)), c q := by
    ext x
    simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · intro hx
      refine ⟨QuotientAddGroup.mk (⟨x, hx⟩ : K), ?_⟩
      rw [hmem]
      have h1 : ((Quotient.out (QuotientAddGroup.mk (⟨x, hx⟩ : K) : K ⧸ H.addSubgroupOf K) : K) :
          K ⧸ H.addSubgroupOf K) = QuotientAddGroup.mk (⟨x, hx⟩ : K) := QuotientAddGroup.out_eq' _
      have h2 := QuotientAddGroup.eq.1 h1
      simpa [AddSubgroup.mem_addSubgroupOf] using h2
    · rintro ⟨q, hq⟩
      have h1 : -((Quotient.out q : K) : G) + x ∈ K := hHK ((hmem q x).1 hq)
      have h2 := K.add_mem (Quotient.out q : K).2 h1
      simpa using h2
  have hd : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (K ⧸ H.addSubgroupOf K))) c := by
    intro q _ q' _ hne
    refine Set.disjoint_left.2 fun x hx hx' => hne ?_
    have h1 := (hmem q x).1 hx
    have h2 := (hmem q' x).1 hx'
    have h3 : -((Quotient.out q : K) : G) + ((Quotient.out q' : K) : G) ∈ H := by
      have := H.add_mem h1 (H.neg_mem h2)
      simpa [add_assoc] using this
    have h4 : ((Quotient.out q : K) : K ⧸ H.addSubgroupOf K) = (Quotient.out q' : K) := by
      apply QuotientAddGroup.eq.2
      simpa [AddSubgroup.mem_addSubgroupOf] using h3
    rwa [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at h4
  have hm : ∀ q ∈ (Finset.univ : Finset (K ⧸ H.addSubgroupOf K)), MeasurableSet (c q) :=
    fun q _ => (measurable_const_add _) hH
  have hμ : ∀ q, μ (c q) = μ (H : Set G) := fun q =>
    MeasureTheory.measure_preimage_add μ _ _
  rw [hU, MeasureTheory.measure_biUnion_finset hd hm]
  simp only [hμ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 2
  rw [AddSubgroup.relIndex, AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]

theorem relIndex_ne_zero_of_isCompact_of_isOpen' {X : Type} [TopologicalSpace X] [AddCommGroup X]
    [IsTopologicalAddGroup X] (A H : AddSubgroup X) (hA : IsCompact (A : Set X)) (hH : IsOpen (H : Set X))
    (_hle : H ≤ A) : H.relIndex A ≠ 0 := by
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have hopen : IsOpen ((H.addSubgroupOf A : AddSubgroup A) : Set A) :=
    hH.preimage continuous_subtype_val
  haveI : Finite (A ⧸ H.addSubgroupOf A) :=
    AddSubgroup.quotient_finite_of_isOpen _ hopen
  exact AddSubgroup.index_ne_zero_of_finite

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ratio_pi {d : ℕ} (X' Y' : AddSubgroup (Fin d → k)) (hXc : IsCompact (X' : Set (Fin d → k)))
    (hXo : IsOpen (X' : Set (Fin d → k))) (L : (Fin d → k) ≃ₗ[k] (Fin d → k))
    (hY : (Y' : Set (Fin d → k)) = L '' (X' : Set (Fin d → k))) :
    (X' ⊓ Y').relIndex X' ≠ 0 ∧ (X' ⊓ Y').relIndex Y' ≠ 0 ∧
      ((X' ⊓ Y').relIndex Y' : ℝ) / ((X' ⊓ Y').relIndex X' : ℝ) =
        (distribHaarChar k (LinearEquiv.det L) : ℝ) := by
  have hLc : Continuous L := L.toLinearMap.continuous_on_pi
  have hLsc : Continuous L.symm := L.symm.toLinearMap.continuous_on_pi
  have hYeq : (Y' : Set (Fin d → k)) = L.symm ⁻¹' (X' : Set (Fin d → k)) := by
    rw [hY]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro h
      exact ⟨L.symm y, h, by simp⟩
  have hYo : IsOpen (Y' : Set (Fin d → k)) := hYeq ▸ hXo.preimage hLsc
  have hYc : IsCompact (Y' : Set (Fin d → k)) := hY ▸ hXc.image hLc
  have hJo : IsOpen ((X' ⊓ Y' : AddSubgroup (Fin d → k)) : Set (Fin d → k)) := by
    rw [AddSubgroup.coe_inf]; exact hXo.inter hYo
  have n1 := relIndex_ne_zero_of_isCompact_of_isOpen' X' (X' ⊓ Y') hXc hJo inf_le_left
  have n2 := relIndex_ne_zero_of_isCompact_of_isOpen' Y' (X' ⊓ Y') hYc hJo inf_le_right
  refine ⟨n1, n2, ?_⟩
  borelize (Fin d → k)
  let μ : Measure (Fin d → k) := Measure.addHaar
  have e1 := measure_eq_relIndex_mul' _ μ (X' ⊓ Y') X' inf_le_left hJo.measurableSet n1
  have e2 := measure_eq_relIndex_mul' _ μ (X' ⊓ Y') Y' inf_le_right hJo.measurableSet n2
  have e3 : μ (Y' : Set (Fin d → k)) = distribHaarChar (Fin d → k) L * μ (X' : Set (Fin d → k)) := by
    rw [distribHaarChar_mul μ L, hY]
    rfl
  rw [GroundTheory.Automorphic.Measures.distribHaarChar_pi_eq] at e3
  have hJ0 : μ ((X' ⊓ Y' : AddSubgroup (Fin d → k)) : Set (Fin d → k)) ≠ 0 :=
    hJo.measure_ne_zero μ ⟨0, (X' ⊓ Y').zero_mem⟩
  have hJt : μ ((X' ⊓ Y' : AddSubgroup (Fin d → k)) : Set (Fin d → k)) ≠ ⊤ :=
    ne_top_of_le_ne_top hXc.measure_lt_top.ne (measure_mono (by simp [AddSubgroup.coe_inf]))
  have key : ((X' ⊓ Y').relIndex Y' : ENNReal) =
      (distribHaarChar k (LinearEquiv.det L) : ENNReal) * ((X' ⊓ Y').relIndex X' : ENNReal) := by
    have h := e3
    rw [e1, e2, ← mul_assoc] at h
    exact (ENNReal.mul_left_inj hJ0 hJt).1 h
  have key' := congrArg ENNReal.toReal key
  rw [ENNReal.toReal_mul] at key'
  simp only [ENNReal.toReal_natCast, ENNReal.coe_toReal] at key'
  rw [key', mul_div_assoc, div_self (by exact_mod_cast n1), mul_one]

end PositivityTheory.RgUd.T.Nil.Orb.BModbound
