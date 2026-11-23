import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsIntValuationLtOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

attribute [local instance] MvPolynomial.weightedGradedAlgebra

namespace RegularityValuationCentre

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ltIdeal_one_isPrime {R Γ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ] (v : Valuation R Γ) :
    (v.ltIdeal 1).IsPrime := by
  refine ⟨fun h => ?_, fun {x y} hxy => ?_⟩
  · have h1 : (1 : v.integer) ∈ v.ltIdeal 1 := h ▸ Submodule.mem_top
    simp [Valuation.mem_ltIdeal_iff] at h1
  · simp only [Valuation.mem_ltIdeal_iff, Units.val_one] at hxy ⊢
    by_contra hc
    push Not at hc
    have hx : v x = 1 := le_antisymm x.2 hc.1
    have hy : v y = 1 := le_antisymm y.2 hc.2
    simp [Subring.coe_mul, map_mul, hx, hy] at hxy

def tWeight [DecidableEq K] (k : K) : K → ℕ := fun k' => if k' = k then 1 else 0

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem specMap_component [DecidableEq K] {E : Type*} [Field E] (ψ : MRing ι →+* E) (k : K) (d : ℕ)
    (g : MRing ι) :
    RegularityFunctionFieldNumber.specMap ψ ∅ (weightedHomogeneousComponent (blockWeight k) d g) =
      weightedHomogeneousComponent (tWeight k) d (RegularityFunctionFieldNumber.specMap ψ ∅ g) := by
  induction g using MvPolynomial.induction_on' with
  | monomial m c =>
    have hX : ∀ p : Σ k, ι k, IsWeightedHomogeneous (tWeight k)
        (RegularityFunctionFieldNumber.cS E ∅ p.1 * MvPolynomial.C (ψ (X p))) (tWeight k p.1) := by
      intro p
      simp only [RegularityFunctionFieldNumber.cS, Finset.notMem_empty, if_false]
      rw [mul_comm]
      exact (isWeightedHomogeneous_X E (tWeight k) p.1).C_mul _
    have hh : IsWeightedHomogeneous (tWeight k) (RegularityFunctionFieldNumber.specMap ψ ∅ (monomial m c))
        (Finsupp.weight (blockWeight k) m) := by
      rw [RegularityFunctionFieldNumber.specMap, aeval_monomial, Finsupp.weight_apply, Finsupp.prod, Finsupp.sum,
        show algebraMap ℤ (MvPolynomial K E) c = MvPolynomial.C (c : E) by simp]
      exact (IsWeightedHomogeneous.prod _ _ _ fun p _ => (hX p).pow (m p)).C_mul _
    have hm : IsWeightedHomogeneous (blockWeight k) (monomial m c) (Finsupp.weight (blockWeight k) m) :=
      isWeightedHomogeneous_monomial _ _ _ rfl
    by_cases h : d = Finsupp.weight (blockWeight k) m
    · rw [h, hm.weightedHomogeneousComponent_same, hh.weightedHomogeneousComponent_same]
    · rw [hm.weightedHomogeneousComponent_ne d h, hh.weightedHomogeneousComponent_ne d h, map_zero]
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, map_add (RegularityFunctionFieldNumber.specMap ψ ∅) p q]
    exact ((weightedHomogeneousComponent (R := E) (tWeight k) d).map_add _ _).symm

set_option backward.isDefEq.respectTransparency.types false in

theorem ker_isMultiHomogIdeal [DecidableEq K] {E : Type*} [Field E] (ψ : MRing ι →+* E) :
    IsMultiHomogIdeal (RingHom.ker (RegularityFunctionFieldNumber.specMap ψ ∅)) := by
  refine isMultiHomogIdeal_of_isHomogeneous fun k d g hg => ?_
  have hc : weightedHomogeneousComponent (blockWeight k) d g ∈ RingHom.ker (RegularityFunctionFieldNumber.specMap ψ ∅) := by
    rw [RingHom.mem_ker] at hg ⊢
    rw [specMap_component, hg, map_zero]
  rw [← weightedDecomposition.decompose'_apply] at hc
  exact hc

end RegularityValuationCentre

set_option maxHeartbeats 400000 in
open regularityEmbedding_holds in

theorem RegularityValuationCentre.proof : RegularityValuationCentre.Statement := by
  intro K _ ι _ P hP Γ _ v n hn
  classical
  obtain ⟨hPp, hPh, hPr⟩ := hP
  have := hPp
  have hX0 : ∀ {f : MRing ι}, f ∉ P → toFrac P f ≠ 0 := fun hf h => hf (toFrac_eq_zero.mp h)

  have hratio : ∀ (p : Σ k, ι k) (i : ι p.1), (X ⟨p.1, i⟩ : MRing ι) ∉ P → ∃ x : funField P,
      (x : FractionRing (MRing ι ⧸ P)) * toFrac P (X ⟨p.1, i⟩) = toFrac P (X p) := fun p i hi =>
    exists_funField_mul_eq (isMultiHomog_X_single p.1 p.2) (isMultiHomog_X_single p.1 i) hi
  choose j0 hj0 using hPr
  choose s hs using fun p : Σ k, ι k => hratio p (j0 p.1) (hj0 p.1)

  have hj : ∀ k, ∃ i, (X ⟨k, i⟩ : MRing ι) ∉ P ∧
      ∀ i', (X ⟨k, i'⟩ : MRing ι) ∉ P → v (s ⟨k, i'⟩) ≤ v (s ⟨k, i⟩) := by
    intro k
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun i => (X ⟨k, i⟩ : MRing ι) ∉ P)
      (fun i => v (s ⟨k, i⟩)) ⟨j0 k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj0 k⟩⟩
    exact ⟨i, (Finset.mem_filter.mp hi).2,
      fun i' hi' => hmax i' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩)⟩
  choose j hjP hjmax using hj
  choose r hr using fun p : Σ k, ι k => hratio p (j p.1) (hjP p.1)

  have hrle : ∀ p, v (r p) ≤ 1 := by
    intro p
    by_cases hp : (X p : MRing ι) ∈ P
    · have h0 : r p = 0 := Subtype.ext <|
        (mul_eq_zero.mp ((hr p).trans (toFrac_eq_zero.mpr hp))).resolve_right (hX0 (hjP p.1))
      simp [h0]
    · obtain ⟨t, ht⟩ := hratio ⟨p.1, j0 p.1⟩ (j p.1) (hjP p.1)
      have hs' := hs ⟨p.1, j p.1⟩
      dsimp only at ht hs'
      have hst : s ⟨p.1, j p.1⟩ * t = 1 := Subtype.ext <| mul_right_cancel₀ (hX0 (hjP p.1)) <| by
        rw [Subring.coe_mul, Subring.coe_one, mul_assoc, ht, hs', one_mul]
      have hrs : r p * s ⟨p.1, j p.1⟩ = s p := Subtype.ext <| mul_right_cancel₀ (hX0 (hj0 p.1)) <| by
        rw [Subring.coe_mul, mul_assoc, hs', hr, hs]
      have hvs : v (s ⟨p.1, j p.1⟩) ≠ 0 := fun h => by
        have h1 := congrArg v hst
        rw [map_mul, h, zero_mul, map_one] at h1
        exact zero_ne_one h1
      have hle : v (r p) * v (s ⟨p.1, j p.1⟩) ≤ 1 * v (s ⟨p.1, j p.1⟩) := by
        rw [← map_mul, hrs, one_mul]
        exact hjmax p.1 p.2 hp
      exact le_of_mul_le_mul_right hle (zero_lt_iff.mpr hvs)

  have hψle : ∀ g, chartHom r g ∈ v.integer := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [chartHom]
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | mul_X f p hf =>
      rw [map_mul]
      exact mul_mem hf (by simpa [chartHom] using (Valuation.mem_integer_iff v (r p)).mpr (hrle p))
  have : (v.ltIdeal 1).IsPrime := RegularityValuationCentre.ltIdeal_one_isPrime v

  obtain ⟨E, _, ψE, hψE⟩ : ∃ (E : Type) (_ : Field E) (ψE : MRing ι →+* E),
      ∀ g, ψE g = 0 ↔ v (chartHom r g) < 1 := by
    refine ⟨FractionRing (v.integer ⧸ v.ltIdeal 1), inferInstance, (algebraMap (v.integer ⧸ v.ltIdeal 1) _).comp
      ((Ideal.Quotient.mk (v.ltIdeal 1)).comp ((chartHom r).codRestrict v.integer hψle)), fun g => ?_⟩
    rw [RingHom.comp_apply, RingHom.comp_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _),
      Ideal.Quotient.eq_zero_iff_mem, Valuation.mem_ltIdeal_iff, Units.val_one]
    rfl

  have hform : ∀ (g : MRing ι) (a : K → ℕ), IsMultiHomog g a →
      (g ∈ RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅) ↔ v (chartHom r g) < 1) := by
    intro g a hg
    rw [RingHom.mem_ker, RegularityFunctionFieldNumber.specMap_form ψE ∅ hg, ← hψE, mul_eq_zero, MvPolynomial.C_eq_zero]
    refine or_iff_right (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ ?_)
    simp [RegularityFunctionFieldNumber.cS, MvPolynomial.X_ne_zero]
  have hWp : (RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅)).IsPrime := RingHom.ker_isPrime _
  have hPW : P ≤ RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅) := by
    obtain ⟨S, hS, hPS⟩ := hPh
    refine hPS.le.trans (Ideal.span_le.mpr fun g hg => ?_)
    obtain ⟨a, ha⟩ := hS g hg
    have hgP : g ∈ P := hPS ▸ Ideal.subset_span hg
    rw [SetLike.mem_coe, hform g a ha]
    have h1 := chartHom_mul j r hr ha
    rw [toFrac_eq_zero.mpr hgP] at h1
    have hφ : chartHom r g = 0 :=
      Subtype.ext ((mul_eq_zero.mp h1).resolve_right (toFrac_prod_ne_zero j hjP a))
    rw [hφ, map_zero]
    exact zero_lt_one
  have hC : IsMultiHomog (C n : MRing ι) 0 := fun μ hμ k => by
    rw [mem_support_iff, coeff_C] at hμ
    split_ifs at hμ with h
    · subst h
      simp
    · exact absurd rfl hμ
  refine ⟨RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅),
    ⟨hWp, RegularityValuationCentre.ker_isMultiHomogIdeal ψE, fun k => ⟨j k, ?_⟩⟩, hPW, ?_, fun z hz => ?_⟩
  ·
    have hrj : r ⟨k, j k⟩ = 1 :=
      Subtype.ext (mul_right_cancel₀ (hX0 (hjP k)) ((hr ⟨k, j k⟩).trans (one_mul _).symm))
    rw [hform _ _ (isMultiHomog_X_single k (j k))]
    have hXr : chartHom r (X ⟨k, j k⟩) = r ⟨k, j k⟩ := eval₂Hom_X' _ _ _
    rw [hXr, hrj, Valuation.map_one]
    exact lt_irrefl 1
  · rw [hform _ 0 hC]
    have hCn : chartHom r (C n) = (n : funField P) := eval₂Hom_C _ _ _
    rw [hCn]
    exact hn
  ·
    obtain ⟨u, w, a, hu, hw, hwW, e⟩ := LocRingFrac.proof K ι P _ hPp hWp hPW z hz
    have hzw : z * chartHom r w = chartHom r u :=
      Subtype.ext <| mul_right_cancel₀ (toFrac_prod_ne_zero j hjP a) <| by
        rw [Subring.coe_mul, mul_assoc, chartHom_mul j r hr hw, chartHom_mul j r hr hu]
        exact e
    have hvw : v (chartHom r w) = 1 :=
      le_antisymm (hψle w) (not_lt.mp fun h => hwW ((hform w a hw).mpr h))
    have h1 := congrArg v hzw
    rw [map_mul, hvw, mul_one] at h1
    exact h1 ▸ hψle u

end

end GroundTheory.Heights₂.Heights.Inter
