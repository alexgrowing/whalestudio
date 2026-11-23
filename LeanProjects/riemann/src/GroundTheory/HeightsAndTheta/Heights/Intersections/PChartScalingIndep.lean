import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CurvePt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StChartScalingIndep
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace ChartScalingIndep

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {K : Type} [Fintype K] [DecidableEq K]
  {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isHomogeneous_mw {V : Ideal (MRingOver F ι)} (hV : IsMultiHomogIdeal V) :
    V.IsHomogeneous (weightedHomogeneousSubmodule F (mw (ι := ι))) := by
  obtain ⟨S, hS, rfl⟩ := hV
  refine Ideal.homogeneous_span _ S fun f hf => ?_
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨a, mem_weighted_of_isMultiHomog ha⟩

theorem coeff_eq_zero (x : (Σ k, ι k) → Ω) (i : ∀ k, ι k) (hx : ∀ k, x ⟨k, i k⟩ ≠ 0)
    (hV : IsMultiHomogIdeal (RingHom.ker (aeval x : MRingOver F ι →ₐ[F] Ω)))
    (s : Finset (K →₀ ℕ)) (g : (K →₀ ℕ) → MRingOver F ι)
    (hs : ∑ α ∈ s, aeval (fun q => x q / x ⟨q.1, i q.1⟩) (g α) * ∏ k, x ⟨k, i k⟩ ^ α k = 0) :
    ∀ β ∈ s, aeval (fun q => x q / x ⟨q.1, i q.1⟩) (g β) = 0 := by
  set y : (Σ k, ι k) → Ω := fun q => x q / x ⟨q.1, i q.1⟩ with hy
  have hxy : x = fun q => x ⟨q.1, i q.1⟩ * y q := by
    funext q
    show x q = x ⟨q.1, i q.1⟩ * (x q / x ⟨q.1, i q.1⟩)
    rw [mul_div_cancel₀ _ (hx q.1)]

  choose e₀ he₀ using fun α => exists_homog_chart (⊥ : Ideal (MRingOver F ι)) i (g α)
  set M : K → ℕ := s.sup e₀ with hM
  have hGex : ∀ α, ∃ G : MRingOver F ι, α ∈ s →
      G ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) M ∧
        Ideal.Quotient.mk (chartIdeal ⊥ i) G = Ideal.Quotient.mk (chartIdeal ⊥ i) (g α) := by
    intro α
    by_cases hα : α ∈ s
    · obtain ⟨G, h1, h2⟩ := he₀ α M (Finset.le_sup (f := e₀) hα)
      exact ⟨G, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hα⟩
  choose G hG using hGex
  have hker : chartIdeal (⊥ : Ideal (MRingOver F ι)) i ≤
      RingHom.ker (aeval y : MRingOver F ι →ₐ[F] Ω) := by
    unfold chartIdeal
    refine sup_le bot_le (Ideal.span_le.mpr ?_)
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, aeval_X, map_one]
    show x ⟨k, i k⟩ / x ⟨k, i k⟩ - 1 = 0
    rw [div_self (hx k), sub_self]
  have hGx : ∀ α ∈ s, aeval x (G α) = (∏ k, x ⟨k, i k⟩ ^ M k) * aeval y (g α) := by
    intro α hα
    have h0 := hker (Ideal.Quotient.eq.mp (hG α hα).2)
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h0
    rw [← h0]
    have h := aeval_blockScale (isMultiHomog_of_mem_weighted (hG α hα).1) (fun k => x ⟨k, i k⟩) y
    exact (congrArg (fun z => aeval z (G α)) hxy).trans h
  have hxc : ∀ α : K →₀ ℕ,
      aeval x (∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ α k) = ∏ k, x ⟨k, i k⟩ ^ α k := by
    intro α
    simp [map_prod]
  have hcM : (∏ k, x ⟨k, i k⟩ ^ M k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hx k)

  have hH : (∑ α ∈ s, G α * ∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ α k) ∈
      RingHom.ker (aeval x : MRingOver F ι →ₐ[F] Ω) := by
    rw [RingHom.mem_ker, map_sum]
    calc ∑ α ∈ s, aeval x (G α * ∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ α k)
        = ∑ α ∈ s, (∏ k, x ⟨k, i k⟩ ^ M k) *
            (aeval y (g α) * ∏ k, x ⟨k, i k⟩ ^ α k) :=
          Finset.sum_congr rfl fun α hα => by rw [map_mul, hGx α hα, hxc, mul_assoc]
      _ = 0 := by rw [← Finset.mul_sum, hs, mul_zero]
  have hmem : ∀ α ∈ s, G α * ∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ α k ∈
      weightedHomogeneousSubmodule F (mw (ι := ι)) (M + ⇑α) := fun α hα =>
    SetLike.mul_mem_graded (hG α hα).1 (mem_weighted_of_isMultiHomog (isMultiHomog_coordProd i ⇑α))
  intro β hβ

  have hcomp : weightedHomogeneousComponent (mw (ι := ι)) (M + ⇑β)
      (∑ α ∈ s, G α * ∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ α k) =
        G β * ∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ β k := by
    rw [map_sum, Finset.sum_eq_single β]
    · rw [weightedHomogeneousComponent_of_mem (hmem β hβ), if_pos rfl]
    · intro α hα hne
      rw [weightedHomogeneousComponent_of_mem (hmem α hα), if_neg]
      intro h
      exact hne (DFunLike.coe_injective (add_left_cancel h)).symm
    · intro h
      exact absurd hβ h
  have hβV := weightedHomogeneousComponent_mem_of_mem F (mw (ι := ι)) (isHomogeneous_mw hV) hH (M + ⇑β)
  rw [hcomp, RingHom.mem_ker, map_mul, hGx β hβ, hxc] at hβV
  have hcβ : (∏ k, x ⟨k, i k⟩ ^ β k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hx k)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hβV).resolve_right hcβ)).resolve_left hcM

end ChartScalingIndep

theorem ChartScalingIndep.proof : ChartScalingIndep.Statement := by
  classical
  intro F Ω _ _ _ K _ ι _ x i hx hV
  set y : (Σ k, ι k) → Ω := fun q => x q / x ⟨q.1, i q.1⟩ with hy
  rw [algebraicIndependent_iff]
  intro p hp

  have hq : ∀ α, ∃ a b : MRingOver F ι, aeval y b ≠ 0 ∧
      ((p.coeff α : IntermediateField.adjoin F (Set.range y)) : Ω) * aeval y b = aeval y a := by
    intro α
    obtain ⟨r, hr, t, ht, he⟩ := IntermediateField.mem_adjoin_iff_div.mp (p.coeff α).2
    rw [Algebra.adjoin_range_eq_range_aeval] at hr ht
    obtain ⟨a, rfl⟩ := hr
    obtain ⟨b, rfl⟩ := ht
    change ((p.coeff α : IntermediateField.adjoin F (Set.range y)) : Ω) = aeval y a / aeval y b at he
    by_cases hb : aeval y b = 0
    · refine ⟨0, 1, by simp, ?_⟩
      rw [he, hb, div_zero]
      simp
    · exact ⟨a, b, hb, by rw [he, div_mul_cancel₀ _ hb]⟩
  choose a b hb hab using hq
  set D : MRingOver F ι := ∏ α ∈ p.support, b α with hD
  have hD0 : aeval y D ≠ 0 := by
    rw [hD, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun α _ => hb α
  set g : (K →₀ ℕ) → MRingOver F ι := fun α => a α * ∏ β ∈ p.support.erase α, b β with hg
  have hgD : ∀ α ∈ p.support,
      aeval y (g α) = aeval y D * ((p.coeff α : IntermediateField.adjoin F (Set.range y)) : Ω) := by
    intro α hα
    rw [hg, hD, map_mul, map_prod, map_prod, ← Finset.mul_prod_erase _ _ hα, ← hab α]
    ring
  have h1 : aeval (fun k => x ⟨k, i k⟩) p = ∑ α ∈ p.support,
      ((p.coeff α : IntermediateField.adjoin F (Set.range y)) : Ω) * ∏ k, x ⟨k, i k⟩ ^ α k := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun k => pow_zero _)]
    rfl
  have hsum : ∑ α ∈ p.support, aeval y (g α) * ∏ k, x ⟨k, i k⟩ ^ α k = 0 := by
    calc ∑ α ∈ p.support, aeval y (g α) * ∏ k, x ⟨k, i k⟩ ^ α k
        = aeval y D * aeval (fun k => x ⟨k, i k⟩) p := by
          rw [h1, Finset.mul_sum]
          exact Finset.sum_congr rfl fun α hα => by rw [hgD α hα, mul_assoc]
      _ = 0 := by rw [hp, mul_zero]
  have h0 := ChartScalingIndep.coeff_eq_zero x i hx hV p.support g hsum
  refine MvPolynomial.ext _ _ fun α => ?_
  rw [coeff_zero]
  by_cases hα : α ∈ p.support
  · have h2 := h0 α hα
    rw [hgD α hα] at h2
    have h3 := (mul_eq_zero.mp h2).resolve_left hD0
    exact_mod_cast h3
  · exact notMem_support_iff.mp hα

end GroundTheory.Heights₂.Heights.Inter
