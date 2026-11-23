import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullConeDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageHilb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial BlockImageHilb

noncomputable section

namespace PullConeDegree

section Lemmas

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  [CharZero Ω]

omit [CharZero Ω] in

theorem isWeightedHomogeneous_of_isMultiHomog {f : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ}
    (hf : IsMultiHomog f a) : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a := by
  intro m hm
  funext k
  rw [weight_blockWeight_apply]
  exact hf m (mem_support_iff.mpr hm) k

omit [CharZero Ω] in

theorem isMultiHomog_of_isWeightedHomogeneous {f : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) : IsMultiHomog f a := by
  intro m hm k
  rw [← weight_blockWeight_apply, hf (mem_support_iff.mp hm)]

omit [DecidableEq K] [CharZero Ω] in

theorem prod_X_pow_eq_monomial (a : K → ℕ) :
    (∏ k, MvPolynomial.X k ^ a k : MvPolynomial K Ω) = monomial (Finsupp.equivFunOnFinite.symm a) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp

theorem coeff_mConeMapQ (y : (Σ k, ι k) → Ω) (f : MvPolynomial (Σ k, ι k) ℚ) (n : K → ℕ) :
    coeff (Finsupp.equivFunOnFinite.symm n) (mConeMapQ y f) =
      aeval y (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) n f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial m r =>
    have hm := isWeightedHomogeneous_monomial (NumbersDVR.blockWeight ι) m r rfl
    rw [mConeMapQ_eq y hm, prod_X_pow_eq_monomial, C_mul_monomial, mul_one, coeff_monomial,
      weightedHomogeneousComponent_of_mem (n := Finsupp.weight (NumbersDVR.blockWeight ι) m) hm]
    by_cases h : n = Finsupp.weight (NumbersDVR.blockWeight ι) m
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun h' => h (Finsupp.equivFunOnFinite.symm.injective h').symm), map_zero]
  | add p q hp hq => rw [map_add, coeff_add, hp, hq, map_add, map_add]

omit [DecidableEq K] [CharZero Ω] in

theorem exists_dvd_monomial (N : ℕ) (hne : ∀ k, Nonempty (ι k)) (μ : (Σ k, ι k) →₀ ℕ)
    (hμ : ∀ k, N * Fintype.card (ι k) ≤ ∑ i, μ ⟨k, i⟩) (r : ℚ) :
    ∃ c : ∀ k, ι k, (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ^ N ∣ monomial μ r := by
  have hc : ∀ k, ∃ i, N ≤ μ ⟨k, i⟩ := by
    intro k
    by_contra h
    simp only [not_exists, not_le] at h
    have hlt := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α := ι k)) (fun i _ => h i)
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm] at hlt
    exact absurd (hμ k) (not_le.mpr hlt)
  choose c hc using hc
  refine ⟨c, ?_⟩
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun i => by simp), Fintype.prod_sigma, ← Finset.prod_pow]
  refine Dvd.dvd.mul_left (Finset.prod_dvd_prod_of_dvd _ _ fun k _ => ?_) _
  exact (pow_dvd_pow _ (hc k)).trans
    (Finset.dvd_prod_of_mem (fun i => (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) ℚ) ^ μ ⟨k, i⟩) (Finset.mem_univ (c k)))

end Lemmas

theorem proof : PullConeDegree.Statement := by
  classical
  intro K _ ι _ Ω _ _ y D e L N hy hL hN d g hg hd
  have hne : ∀ k, Nonempty (ι k) := fun k => (hy k).elim fun i _ => ⟨i⟩

  have hgI : g ∈ coneNullIdeal y L := by
    rw [g.as_sum]
    refine Ideal.sum_mem _ fun μ hμ => ?_
    obtain ⟨c, hc⟩ := exists_dvd_monomial N hne μ
      (fun k => by rw [hg μ hμ k]; have := hd k; omega) (coeff μ g)
    exact Ideal.mem_of_dvd _ hc (hN c)
  have hI : coneNullIdeal y L = RingHom.ker (mConeMapQ y) ⊔
      Ideal.span (Set.range fun j => map (Int.castRingHom ℚ) (L j)) := by
    rw [coneNullIdeal, Ideal.span_union, ← map_mCoordIdeal]
    rfl
  rw [hI, Submodule.mem_sup] at hgI
  obtain ⟨u, hu, v, hv, huv⟩ := hgI
  obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp hv

  have hmapL : ∀ j, mConeMapQ y (map (Int.castRingHom ℚ) (L j)) =
      monomial (Finsupp.equivFunOnFinite.symm e) (aeval y (L j)) := by
    intro j
    have h : IsMultiHomog (map (Int.castRingHom ℚ) (L j)) e := fun m hm => hL j m (support_map_subset _ _ hm)
    rw [mConeMapQ_eq y (isWeightedHomogeneous_of_isMultiHomog h), prod_X_pow_eq_monomial, C_mul_monomial, mul_one,
      ← algebraMap_int_eq, aeval_map_algebraMap]
  have hψg : mConeMapQ y g =
      ∑ j, mConeMapQ y (b j) * monomial (Finsupp.equivFunOnFinite.symm e) (aeval y (L j)) := by
    rw [← huv, map_add, RingHom.mem_ker.mp hu, zero_add, ← hb, map_sum]
    simp only [map_mul, hmapL]

  refine ⟨fun j => weightedHomogeneousComponent (NumbersDVR.blockWeight ι) (d - e) (b j),
    fun j => isMultiHomog_of_isWeightedHomogeneous (weightedHomogeneousComponent_isWeightedHomogeneous _ _), ?_⟩
  have hc := congrArg (coeff (Finsupp.equivFunOnFinite.symm d)) hψg
  rw [mConeMapQ_eq y (isWeightedHomogeneous_of_isMultiHomog hg), prod_X_pow_eq_monomial, C_mul_monomial, mul_one,
    coeff_monomial, if_pos rfl, coeff_sum] at hc
  rw [hc]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hle : Finsupp.equivFunOnFinite.symm e ≤ Finsupp.equivFunOnFinite.symm d :=
    Finsupp.le_def.mpr fun k => by simp only [Finsupp.coe_equivFunOnFinite_symm]; have := hd k; omega
  have hsub : Finsupp.equivFunOnFinite.symm d - Finsupp.equivFunOnFinite.symm e =
      Finsupp.equivFunOnFinite.symm (d - e) := by
    ext k
    simp
  rw [coeff_mul_monomial', if_pos hle, hsub, coeff_mConeMapQ]

end PullConeDegree

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
