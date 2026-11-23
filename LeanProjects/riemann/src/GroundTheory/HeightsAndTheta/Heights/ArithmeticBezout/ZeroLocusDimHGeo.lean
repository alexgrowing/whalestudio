import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Metric Filter Topology Finset

noncomputable section

namespace ZeroLocusDimH

theorem root_lipschitz_core {E : Type*} [NormedAddCommGroup E] (N : ℕ) (c : ℕ → E → ℂ) (y₀ : E)
    (t₀ : ℂ) (hcont : ∀ k, Continuous (c k))
    (hlip : ∀ k, ∃ L : NNReal, ∃ T ∈ 𝓝 y₀, LipschitzOnWith L (c k) T)
    (hder : ∑ k ∈ range N, c k y₀ * ((k : ℂ) * t₀ ^ (k - 1)) ≠ 0) :
    ∃ δ > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ y y' : E, ∀ t t' : ℂ,
      dist y y₀ < δ → dist y' y₀ < δ → dist t t₀ < δ → dist t' t₀ < δ →
      ∑ k ∈ range N, c k y * t ^ k = 0 → ∑ k ∈ range N, c k y' * t' ^ k = 0 →
      ‖t - t'‖ ≤ K * ‖y - y'‖ := by
  set D : E × ℂ × ℂ → ℂ := fun z =>
    ∑ k ∈ range N, c k z.1 * ∑ j ∈ range k, z.2.1 ^ j * z.2.2 ^ (k - 1 - j) with hDdef
  have hDc : Continuous D := by
    refine continuous_finsetSum _ fun k _ => ((hcont k).comp continuous_fst).mul ?_
    exact continuous_finsetSum _ fun j _ => by fun_prop
  set D0 := ∑ k ∈ range N, c k y₀ * ((k : ℂ) * t₀ ^ (k - 1)) with hD0def
  have hDz : D (y₀, t₀, t₀) = D0 := by
    simp only [hDdef, hD0def]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [Finset.sum_congr rfl (g := fun _ => t₀ ^ (k - 1)), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    intro j hj
    rw [← pow_add]
    congr 1
    have := Finset.mem_range.1 hj
    omega
  have hpos : 0 < ‖D0‖ / 2 := by positivity
  obtain ⟨δ2, hδ2, hD⟩ := Metric.continuous_iff.1 hDc (y₀, t₀, t₀) _ hpos
  choose L T hT hLT using hlip
  have hS : (⋂ k ∈ range N, T k) ∈ 𝓝 y₀ := (Filter.biInter_finset_mem _).2 fun k _ => hT k
  obtain ⟨δ1, hδ1, hball⟩ := Metric.mem_nhds_iff.1 hS
  refine ⟨min (min δ1 δ2) 1, by positivity, (∑ k ∈ range N, (L k : ℝ) * (‖t₀‖ + 1) ^ k) / (‖D0‖ / 2),
    by positivity, ?_⟩
  intro y y' t t' hy hy' ht ht' h1 h2
  have hyS : ∀ k ∈ range N, y ∈ T k := by
    have := hball (Metric.mem_ball.2 (lt_of_lt_of_le hy ((min_le_left _ _).trans (min_le_left _ _))))
    simpa using this
  have hyS' : ∀ k ∈ range N, y' ∈ T k := by
    have := hball (Metric.mem_ball.2 (lt_of_lt_of_le hy' ((min_le_left _ _).trans (min_le_left _ _))))
    simpa using this
  have hz : dist (y, t, t') (y₀, t₀, t₀) < δ2 := by
    have e2 : min (min δ1 δ2) 1 ≤ δ2 := (min_le_left _ _).trans (min_le_right _ _)
    rw [Prod.dist_eq, Prod.dist_eq]
    exact max_lt (hy.trans_le e2) (max_lt (ht.trans_le e2) (ht'.trans_le e2))
  have hDlow : ‖D0‖ / 2 ≤ ‖D (y, t, t')‖ := by
    have := hD _ hz
    rw [hDz, dist_eq_norm] at this
    have h3 := norm_sub_norm_le D0 (D (y, t, t'))
    rw [norm_sub_rev] at h3
    linarith
  have ht'b : ‖t'‖ ≤ ‖t₀‖ + 1 := by
    have : dist t' t₀ < 1 := ht'.trans_le (min_le_right _ _)
    rw [dist_eq_norm] at this
    have := norm_le_norm_add_norm_sub' t' t₀
    linarith
  have key : (t - t') * D (y, t, t') = ∑ k ∈ range N, (c k y' - c k y) * t' ^ k := by
    have e1 : (t - t') * D (y, t, t') = ∑ k ∈ range N, c k y * (t ^ k - t' ^ k) := by
      show (t - t') * ∑ k ∈ range N, c k y * ∑ j ∈ range k, t ^ j * t' ^ (k - 1 - j) = _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← geom_sum₂_mul t t' k]
      ring
    rw [e1]
    have : ∑ k ∈ range N, c k y * (t ^ k - t' ^ k) + ∑ k ∈ range N, (c k y - c k y') * t' ^ k =
        ∑ k ∈ range N, c k y * t ^ k - ∑ k ∈ range N, c k y' * t' ^ k := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [h1, h2, sub_zero] at this
    have e3 : ∑ k ∈ range N, (c k y' - c k y) * t' ^ k = -∑ k ∈ range N, (c k y - c k y') * t' ^ k := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e3]
    linear_combination this
  have hbound : ‖t - t'‖ * ‖D (y, t, t')‖ ≤
      (∑ k ∈ range N, (L k : ℝ) * (‖t₀‖ + 1) ^ k) * ‖y - y'‖ := by
    rw [← norm_mul, key, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    rw [norm_mul, norm_pow]
    have hl := (hLT k).dist_le_mul y' (hyS' k hk) y (hyS k hk)
    rw [dist_eq_norm, dist_eq_norm, ← norm_neg (y' - y), neg_sub] at hl
    have hp : ‖t'‖ ^ k ≤ (‖t₀‖ + 1) ^ k := pow_le_pow_left₀ (norm_nonneg _) ht'b k
    calc ‖c k y' - c k y‖ * ‖t'‖ ^ k ≤ ((L k : ℝ) * ‖y - y'‖) * (‖t₀‖ + 1) ^ k :=
          mul_le_mul hl hp (by positivity) (by positivity)
      _ = (L k : ℝ) * (‖t₀‖ + 1) ^ k * ‖y - y'‖ := by ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  calc ‖t - t'‖ * (‖D0‖ / 2) ≤ ‖t - t'‖ * ‖D (y, t, t')‖ :=
        mul_le_mul_of_nonneg_left hDlow (norm_nonneg _)
    _ ≤ _ := hbound

theorem contDiff_eval_mvPolynomial {ι : Type*} [Fintype ι] (q : MvPolynomial ι ℂ) :
    ContDiff ℂ 1 (fun y : ι → ℂ => MvPolynomial.eval y q) := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (contDiff_apply ℂ ℂ i)

def paramMap {n r : ℕ} (π : Fin r → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) : Fin r → ℂ :=
  fun j => MvPolynomial.eval x (π j)

theorem continuous_paramMap {n r : ℕ} (π : Fin r → MvPolynomial (Fin n) ℂ) :
    Continuous (paramMap π) :=
  continuous_pi fun _ => MvPolynomial.continuous_eval _

theorem eval_map_eq_sum {r : ℕ} (Q : Polynomial (MvPolynomial (Fin r) ℂ)) (y : Fin r → ℂ) (t : ℂ) :
    Polynomial.eval t (Q.map (MvPolynomial.eval y)) =
      ∑ k ∈ range (Q.natDegree + 1), MvPolynomial.eval y (Q.coeff k) * t ^ k := by
  rw [Polynomial.eval_eq_sum_range' (n := Q.natDegree + 1)
    (lt_of_le_of_lt (Polynomial.natDegree_map_le) (Nat.lt_succ_self _))]
  simp [Polynomial.coeff_map]

theorem eval_map_derivative_eq_sum {r : ℕ} (Q : Polynomial (MvPolynomial (Fin r) ℂ))
    (y : Fin r → ℂ) (t : ℂ) :
    Polynomial.eval t ((Polynomial.derivative Q).map (MvPolynomial.eval y)) =
      ∑ k ∈ range (Q.natDegree + 1), MvPolynomial.eval y (Q.coeff k) * ((k : ℂ) * t ^ (k - 1)) := by
  rw [← Polynomial.derivative_map, Polynomial.derivative_eval,
    Polynomial.sum_over_range' (n := Q.natDegree + 1) _ (fun _ => by simp)
      (lt_of_le_of_lt (Polynomial.natDegree_map_le) (Nat.lt_succ_self _))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.coeff_map]
  ring

theorem local_antilipschitz {n r : ℕ} (π : Fin r → MvPolynomial (Fin n) ℂ)
    (P : Fin n → Polynomial (MvPolynomial (Fin r) ℂ)) (V : Set (Fin n → ℂ))
    (hV : ∀ x ∈ V, ∀ i, Polynomial.eval (x i) ((P i).map (MvPolynomial.eval (paramMap π x))) = 0)
    (x₀ : Fin n → ℂ)
    (hx₀ : ∀ i, Polynomial.eval (x₀ i)
      ((Polynomial.derivative (P i)).map (MvPolynomial.eval (paramMap π x₀))) ≠ 0) :
    ∃ U ∈ 𝓝 x₀, ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ V ∩ U, ∀ x' ∈ V ∩ U, ‖x - x'‖ ≤ K * ‖paramMap π x - paramMap π x'‖ := by
  have core : ∀ i, ∃ δ > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ y y' : Fin r → ℂ, ∀ t t' : ℂ,
      dist y (paramMap π x₀) < δ → dist y' (paramMap π x₀) < δ → dist t (x₀ i) < δ →
      dist t' (x₀ i) < δ →
      ∑ k ∈ range ((P i).natDegree + 1), MvPolynomial.eval y ((P i).coeff k) * t ^ k = 0 →
      ∑ k ∈ range ((P i).natDegree + 1), MvPolynomial.eval y' ((P i).coeff k) * t' ^ k = 0 →
      ‖t - t'‖ ≤ K * ‖y - y'‖ := fun i =>
    root_lipschitz_core _ (fun k y => MvPolynomial.eval y ((P i).coeff k)) _ _
      (fun k => MvPolynomial.continuous_eval _)
      (fun k => by
        obtain ⟨L, T, hT, hL⟩ :=
          ((contDiff_eval_mvPolynomial ((P i).coeff k)).contDiffAt (x := paramMap π x₀)).exists_lipschitzOnWith
        exact ⟨L, T, hT, hL⟩)
      (by rw [← eval_map_derivative_eq_sum]; exact hx₀ i)
  choose δ hδ K hK hcore using core
  refine ⟨{x | ∀ i, dist (paramMap π x) (paramMap π x₀) < δ i ∧ dist (x i) (x₀ i) < δ i}, ?_,
    ∑ i, K i, Finset.sum_nonneg fun i _ => hK i, ?_⟩
  · refine Filter.eventually_all.2 fun i => ?_
    exact (((continuous_paramMap π).tendsto x₀).eventually (Metric.ball_mem_nhds _ (hδ i))).and
      (((continuous_apply i).tendsto x₀).eventually (Metric.ball_mem_nhds _ (hδ i)))
  rintro x ⟨hxV, hxU⟩ x' ⟨hxV', hxU'⟩
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ => hK i) (norm_nonneg _))).2 fun i => ?_
  have h1 := hV x hxV i
  have h2 := hV x' hxV' i
  rw [eval_map_eq_sum] at h1 h2
  have := hcore i _ _ _ _ (hxU i).1 (hxU' i).1 (hxU i).2 (hxU' i).2 h1 h2
  rw [Pi.sub_apply]
  refine this.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact Finset.single_le_sum (f := K) (fun j _ => hK j) (Finset.mem_univ i)

theorem dimH_le_of_local_antilipschitz {n r : ℕ} (f : (Fin n → ℂ) → (Fin r → ℂ))
    (S : Set (Fin n → ℂ))
    (h : ∀ x₀ ∈ S, ∃ U ∈ 𝓝 x₀, ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ S ∩ U, ∀ x' ∈ S ∩ U, ‖x - x'‖ ≤ K * ‖f x - f x'‖) :
    dimH S ≤ 2 * (r : ENNReal) := by
  by_contra hlt0
  have hlt := not_le.1 hlt0
  obtain ⟨x₀, hx₀, hall⟩ := exists_mem_nhdsWithin_lt_dimH_of_lt_dimH hlt
  obtain ⟨U, hU, K, hK, hKU⟩ := h x₀ hx₀
  have hlt' := hall (S ∩ U) (inter_mem_nhdsWithin S hU)
  refine (not_le.2 hlt') ?_
  let g : (S ∩ U : Set (Fin n → ℂ)) → (Fin r → ℂ) := fun a => f a
  have hg : AntilipschitzWith ⟨K, hK⟩ g := by
    refine AntilipschitzWith.of_le_mul_dist fun a b => ?_
    rw [Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    exact hKU a a.2 b b.2
  have e1 : dimH (S ∩ U) = dimH (Set.univ : Set (S ∩ U : Set (Fin n → ℂ))) := by
    rw [← (isometry_subtype_coe).dimH_image Set.univ, Subtype.coe_image_univ]
  have hfin : Module.finrank ℝ (Fin r → ℂ) = 2 * r := by
    rw [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
  calc dimH (S ∩ U) = dimH (Set.univ : Set (S ∩ U : Set (Fin n → ℂ))) := e1
    _ ≤ dimH (g '' Set.univ) := hg.le_dimH_image _
    _ ≤ dimH (Set.univ : Set (Fin r → ℂ)) := dimH_mono (Set.subset_univ _)
    _ = Module.finrank ℝ (Fin r → ℂ) := Real.dimH_univ_eq_finrank _
    _ = 2 * (r : ENNReal) := by rw [hfin]; push_cast; ring

theorem dimH_simple_roots_le {n r : ℕ} (π : Fin r → MvPolynomial (Fin n) ℂ)
    (P : Fin n → Polynomial (MvPolynomial (Fin r) ℂ)) (V : Set (Fin n → ℂ))
    (hV : ∀ x ∈ V, ∀ i, Polynomial.eval (x i) ((P i).map (MvPolynomial.eval (paramMap π x))) = 0) :
    dimH {x | x ∈ V ∧ ∀ i, Polynomial.eval (x i)
      ((Polynomial.derivative (P i)).map (MvPolynomial.eval (paramMap π x))) ≠ 0} ≤
      2 * (r : ENNReal) := by
  refine dimH_le_of_local_antilipschitz (paramMap π) _ fun x₀ hx₀ => ?_
  obtain ⟨U, hU, K, hK, hKU⟩ := local_antilipschitz π P V hV x₀ hx₀.2
  exact ⟨U, hU, K, hK, fun x hx x' hx' => hKU x ⟨hx.1.1, hx.2⟩ x' ⟨hx'.1.1, hx'.2⟩⟩

end ZeroLocusDimH

end

end GroundTheory.Heights₂.Heights
