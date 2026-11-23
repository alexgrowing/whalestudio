import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsChartRankAdjoin
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumPoint
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace ChartRankAdjoin

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ'] (z : (Σ k, ι k) → Φ') (j : ∀ k, ι k)

def affCoord : (Σ k, ι k) → Φ' := fun q => z q / z ⟨q.1, j q.1⟩

variable {z j}

theorem aeval_monomial_mul (hz : ∀ k, z ⟨k, j k⟩ ≠ 0) (m : (Σ k, ι k) →₀ ℕ) :
    aeval (affCoord z j) (monomial m (1 : Φ)) *
        ∏ k, z ⟨k, j k⟩ ^ (Finsupp.weight (NumbersDVR.blockWeight ι) m k) =
      aeval z (monomial m (1 : Φ)) := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add m m' hm hm' =>
    rw [← mul_one (1 : Φ), ← monomial_mul, map_mul, map_mul, map_add, ← hm, ← hm']
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring
  | single p n =>
    rw [← X_pow_eq_monomial, map_pow, map_pow, Finsupp.weight_single,
      Fintype.prod_eq_single p.1 (fun k hk => by simp [NumbersDVR.blockWeight, hk])]
    simp only [affCoord, aeval_X, NumbersDVR.blockWeight, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one, div_pow]
    rw [div_mul_cancel₀ _ (pow_ne_zero _ (hz p.1))]

theorem aeval_mul_of_isMultiHomog [∀ k, Fintype (ι k)] (hz : ∀ k, z ⟨k, j k⟩ ≠ 0) {h : MRingOver Φ ι} {a : K → ℕ}
    (hh : IsMultiHomog h a) : aeval (affCoord z j) h * ∏ k, z ⟨k, j k⟩ ^ a k = aeval z h := by
  have hw := (Bridge.isMultiHomog_iff h a).mpr hh
  conv_rhs => rw [h.as_sum]
  conv_lhs => rw [h.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw' : Finsupp.weight (NumbersDVR.blockWeight ι) m = a := hw (mem_support_iff.mp hm)
  have hmon : monomial m (coeff m h) = coeff m h • monomial m (1 : Φ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hmon, map_smul, map_smul, smul_mul_assoc, ← hw', aeval_monomial_mul hz]

theorem chartIdeal_eq_ker [∀ k, Fintype (ι k)] (hz : ∀ k, z ⟨k, j k⟩ ≠ 0)
    (hP : IsMultiHomogIdeal (RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ'))) :
    chartIdeal (RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ')) j =
      RingHom.ker (aeval (affCoord z j) : MRingOver Φ ι →ₐ[Φ] Φ') := by
  have hprod : ∀ a : K → ℕ, ∏ k, z ⟨k, j k⟩ ^ a k ≠ 0 :=
    fun a => Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hz k)
  have hunit : Ideal.span (Set.range fun k => (X ⟨k, j k⟩ : MRingOver Φ ι) - 1) ≤
      RingHom.ker (aeval (affCoord z j) : MRingOver Φ ι →ₐ[Φ] Φ') := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, aeval_X, affCoord]
    rw [div_self (hz k), sub_self]
  refine le_antisymm (sup_le ?_ hunit) fun f hf => ?_
  · obtain ⟨S, hS, hPS⟩ := hP
    rw [hPS, Ideal.span_le]
    intro s hs
    obtain ⟨a, ha⟩ := hS s hs
    have hsP : s ∈ RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ') := by
      rw [hPS]; exact Ideal.subset_span hs
    have h1 := aeval_mul_of_isMultiHomog hz ha
    rw [RingHom.mem_ker.mp hsP] at h1
    exact RingHom.mem_ker.mpr ((mul_eq_zero.mp h1).resolve_right (hprod a))
  · obtain ⟨N, hN⟩ := NumbersDVR.IntNumPoint.exists_homog_congr j f
    obtain ⟨h, hh, hc⟩ := hN N le_rfl
    have hfh : f - h ∈ NumbersDVR.IntNumPoint.chartUnitIdeal (F := Φ) j := Ideal.Quotient.eq.mp hc
    have h0 : aeval (affCoord z j) h = 0 := by
      have := RingHom.mem_ker.mp (hunit hfh)
      rwa [map_sub, RingHom.mem_ker.mp hf, zero_sub, neg_eq_zero] at this
    have hhP : h ∈ RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ') := by
      rw [RingHom.mem_ker, ← aeval_mul_of_isMultiHomog hz ((Bridge.isMultiHomog_iff h N).mp hh), h0,
        zero_mul]
    have : f = (f - h) + h := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_right hfh) (Ideal.mem_sup_left hhP)

end ChartRankAdjoin

theorem ChartRankAdjoin.proof : ChartRankAdjoin.Statement := by
  classical
  intro K _ ι _ Φ Φ' _ _ _ z j hz hP
  have hker := ChartRankAdjoin.chartIdeal_eq_ker hz hP
  have e : (fun q : Σ k, ι k => z q / z ⟨q.1, j q.1⟩) = ChartRankAdjoin.affCoord z j := rfl
  rw [e, ptDeg, hker,
    (Ideal.quotientKerEquivRange (aeval (ChartRankAdjoin.affCoord z j) :
      MRingOver Φ ι →ₐ[Φ] Φ')).toLinearEquiv.finrank_eq, aeval_range,
    ← IntermediateField.finrank_eq_finrank_subalgebra]
  by_cases halg : ∀ q, IsAlgebraic Φ (ChartRankAdjoin.affCoord z j q)
  · rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (by rintro _ ⟨q, rfl⟩; exact halg q)]
  · push Not at halg
    obtain ⟨q, hq⟩ := halg
    have hinf : ∀ B : Subalgebra Φ Φ', ChartRankAdjoin.affCoord z j q ∈ B → ¬ Module.Finite Φ B :=
      fun B hB hfin => hq ((IsAlgebraic.of_finite Φ (⟨_, hB⟩ : B)).algHom B.val)
    have h1 : ChartRankAdjoin.affCoord z j q ∈ Algebra.adjoin Φ (Set.range (ChartRankAdjoin.affCoord z j)) :=
      Algebra.subset_adjoin ⟨q, rfl⟩
    have h2 : ChartRankAdjoin.affCoord z j q ∈
        (IntermediateField.adjoin Φ (Set.range (ChartRankAdjoin.affCoord z j))).toSubalgebra :=
      IntermediateField.subset_adjoin Φ _ ⟨q, rfl⟩
    rw [Module.finrank_of_not_finite (hinf _ h1), Module.finrank_of_not_finite (hinf _ h2)]

end GroundTheory.Heights₂.Heights.Inter
