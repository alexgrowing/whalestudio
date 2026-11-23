import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens

noncomputable section

section
open Finset MeasureTheory Set

namespace ReciprocityTheory.ChartRestriction.DS

theorem gaussA_lint_pi_ofReal {ι : Type*} [Fintype ι] {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : ∀ i, E i → ℝ)
    (hf : ∀ i, Integrable (f i) (μ i)) (h0 : ∀ i x, 0 ≤ f i x) :
    ∫⁻ x, ENNReal.ofReal (∏ i, f i (x i)) ∂(Measure.pi μ) = ∏ i, ENNReal.ofReal (∫ x, f i x ∂(μ i)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod_dep hf)
    (ae_of_all _ fun x => Finset.prod_nonneg fun i _ => h0 i _), integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (h0 i))]

theorem gaussA_real_int : Integrable (fun x : ℝ => Real.exp (-x ^ 2)) := by
  simpa using integrable_exp_neg_mul_sq (b := 1) one_pos

theorem gaussA_cfun_eq : (fun z : ℂ => Real.exp (-‖z‖ ^ 2)) =
    (fun p : ℝ × ℝ => Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2)) ∘ Complex.measurableEquivRealProd := by
  funext z
  simp only [Function.comp_apply, Complex.measurableEquivRealProd_apply, ← Real.exp_add]
  congr 1
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem gaussA_cint : Integrable (fun z : ℂ => Real.exp (-‖z‖ ^ 2)) := by
  rw [gaussA_cfun_eq, Complex.volume_preserving_equiv_real_prod.integrable_comp_emb
    Complex.measurableEquivRealProd.measurableEmbedding]
  exact Integrable.mul_prod gaussA_real_int gaussA_real_int

theorem gaussA_cintegral : ∫ z : ℂ, Real.exp (-‖z‖ ^ 2) = Real.pi := by
  have h := Complex.volume_preserving_equiv_real_prod.integral_comp
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2))
  have h2 : ∫ p : ℝ × ℝ, Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2) = Real.pi := by
    rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
      integral_prod_mul (fun x : ℝ => Real.exp (-x ^ 2)) (fun x : ℝ => Real.exp (-x ^ 2))]
    have hg : ∫ x : ℝ, Real.exp (-x ^ 2) = Real.sqrt Real.pi := by
      simpa using integral_gaussian 1
    rw [hg, Real.mul_self_sqrt Real.pi_pos.le]
  rw [gaussA_cfun_eq]
  simpa [Function.comp_def] using h.trans h2

theorem gaussA_rad (a : ℕ) :
    ∫ r in Ioi (0:ℝ), Real.exp (-r ^ 2) * |r| ^ (2 * a + 1) = (a.factorial : ℝ) / 2 := by
  have h := integral_rpow_mul_exp_neg_rpow (p := 2) (q := ((2 * a + 1 : ℕ) : ℝ)) two_pos (by have := (Nat.cast_nonneg (2*a+1) : (0:ℝ) ≤ _); linarith)
  have hc : ∫ r in Ioi (0:ℝ), Real.exp (-r ^ 2) * |r| ^ (2 * a + 1) =
      ∫ x in Ioi (0:ℝ), x ^ (((2 * a + 1 : ℕ) : ℝ)) * Real.exp (-x ^ (2:ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simp only [Real.rpow_natCast, abs_of_pos (mem_Ioi.mp hx)]
    rw [show x ^ (2:ℝ) = x ^ (2:ℕ) by exact_mod_cast Real.rpow_natCast x 2, mul_comm]
  rw [hc, h]
  have : ((((2 * a + 1 : ℕ) : ℝ)) + 1) / 2 = (a : ℝ) + 1 := by push_cast; ring
  rw [this, Real.Gamma_nat_eq_factorial]
  ring

theorem gaussA_rad_int (a : ℕ) :
    IntegrableOn (fun r : ℝ => Real.exp (-r ^ 2) * |r| ^ (2 * a + 1)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := ((2 * a + 1 : ℕ) : ℝ)) (by have := (Nat.cast_nonneg (2*a+1) : (0:ℝ) ≤ _); linarith)
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, abs_of_pos (mem_Ioi.mp hx)]
  ring_nf

end ReciprocityTheory.ChartRestriction.DS

end

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem gaussB_hs_eq_re_trace (M : Matrix (Fin N) (Fin N) ℂ) : hs M = (trace (Mᴴ * M)).re := by
  simp only [hs, trace, Matrix.diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

theorem gaussB_hs_unitary_mul (k : UNgrp N) (M : Matrix (Fin N) (Fin N) ℂ) : hs (toM k * M) = hs M := by
  have hk : inUJ (fun _ : Fin N => true) (toM k) := k.2
  have hJ : Jm (fun _ : Fin N => true) = 1 := by
    unfold Jm; simp
  unfold inUJ at hk
  rw [hJ, Matrix.mul_one] at hk
  rw [gaussB_hs_eq_re_trace, gaussB_hs_eq_re_trace, conjTranspose_mul,
    show Mᴴ * (toM k)ᴴ * (toM k * M) = Mᴴ * ((toM k)ᴴ * toM k) * M by simp only [Matrix.mul_assoc],
    hk, Matrix.mul_one]

theorem gaussB_card_lt : Fintype.card {ab : Fin N × Fin N // ab.1 < ab.2} = N * (N - 1) / 2 := by
  rw [Fintype.card_subtype, Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
  have h1 : ∀ i : Fin N, (∑ j : Fin N, if i < j then 1 else 0) = N - 1 - i := by
    intro i
    rw [← Finset.card_filter, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  simp_rw [h1]
  have h2 : (∑ i : Fin N, (N - 1 - (i : ℕ))) = ∑ i : Fin N, (i : ℕ) := by
    refine Fintype.sum_equiv Fin.revPerm _ _ (fun i => ?_)
    simp only [Fin.revPerm_apply, Fin.val_rev]
    omega
  rw [h2, Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]

theorem gaussB_prod_fact :
    (∏ j : Fin N, (((N - 1 - (j : ℕ)).factorial : ℝ) / 2)) = (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N := by
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [← Fin.prod_univ_eq_prod_range (fun i => (i.factorial : ℝ)) N]
  refine Fintype.prod_equiv Fin.revPerm _ _ (fun i => ?_)
  simp only [Fin.revPerm_apply, Fin.val_rev]
  exact congrArg (fun m : ℕ => ((m.factorial : ℕ) : ℝ)) (by omega)

end ReciprocityTheory.ChartRestriction.DS
