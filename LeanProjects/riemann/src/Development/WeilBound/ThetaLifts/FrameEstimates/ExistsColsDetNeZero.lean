import Development.WeilBound.ThetaLifts.FrameEstimates.IntMvPolynomialCoeffAbsSumMulLe

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_cols_det_ne_zero {K : Type} [Field K] {i d : ℕ} (A : Matrix (Fin i) (Fin d) K)
    (hA : LinearIndependent K A.row) : ∃ c : Fin i → Fin d, Function.Injective c ∧ (A.submatrix id c).det ≠ 0 := by
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K A.col
  haveI : Fintype κ := Fintype.ofInjective a ha
  have hcard : Fintype.card κ = i := by
    rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_cols, hA.rank_matrix, Fintype.card_fin]
  let e := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩
  have hu : IsUnit (A.submatrix id (a ∘ e)) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli.comp e e.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

theorem exists_one_le_emb {x : E} (hx : IsIntegral ℤ x) (h0 : x ≠ 0) : ∃ φ : E →+* ℂ, 1 ≤ ‖φ x‖ := by
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace E, 1 ≤ w x := by
    by_contra hne
    push Not at hne
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    exact absurd (InfinitePlace.one_le_of_lt_one (w := w) (a := (⟨x, hx⟩ : 𝓞 E))
      (fun h => h0 (congrArg Subtype.val h)) fun z _ => hne z) (not_le.2 (hne w))
  exact ⟨w.embedding, by rwa [InfinitePlace.norm_embedding_eq]⟩

theorem sum_lam_le_psum {d y : ℕ} {lam : Fin d → (Fin y → ℝ) →ₗ[ℝ] ℝ} {jx jy : Fin y ↪ Fin d} (h1 : ∀ i j, jx i ≠ jy j)
    (h2 : ∀ i t, lam (jx i) t = t i ∧ lam (jy i) t = -t i) (h3 : ∀ k, (∀ i, jx i ≠ k ∧ jy i ≠ k) → lam k = 0)
    {t : Fin y → ℝ} (ht : t ∈ Cone y) {i : ℕ} {c : Fin i → Fin d} (hc : Function.Injective c) :
    ∑ a, lam (c a) t ≤ psum t i := by
  classical
  have key : ∀ θ : ℝ, 0 ≤ θ → ∑ a, lam (c a) t ≤ ∑ j, max 0 (t j - θ) + i * θ := by
    intro θ hθ
    have e := sum_lam h1 h2 h3 (fun u => max 0 (u - θ)) t
    have e1 : ∀ j, max 0 (-t j - θ) = 0 := fun j => max_eq_left (by linarith [ht.2 j])
    simp only [e1, max_eq_left (show 0 - θ ≤ 0 by linarith), Finset.sum_const_zero, add_zero, mul_zero] at e
    rw [← e]
    have e2 : ∑ a, max 0 (lam (c a) t - θ) ≤ ∑ k, max 0 (lam k t - θ) := by
      exact (Finset.sum_map Finset.univ ⟨c, hc⟩ fun k => max 0 (lam k t - θ)).symm.trans_le
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => le_max_left _ _)
    have e3 : ∑ a, lam (c a) t ≤ ∑ a, (max 0 (lam (c a) t - θ) + θ) :=
      Finset.sum_le_sum fun a _ => by linarith [le_max_right 0 (lam (c a) t - θ)]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at e3
    linarith
  by_cases hi : i < y
  · refine (key (t ⟨i, hi⟩) (ht.2 _)).trans (le_of_eq ?_)
    have e : ∀ j : Fin y, max 0 (t j - t ⟨i, hi⟩) =
        (if j.val < i then t j else 0) - if j.val < i then t ⟨i, hi⟩ else 0 := by
      intro j
      split_ifs with h
      · exact max_eq_right (sub_nonneg.2 (ht.1 (show j ≤ ⟨i, hi⟩ from h.le)))
      · rw [sub_zero]
        exact max_eq_left (sub_nonpos.2 (ht.1 (show (⟨i, hi⟩ : Fin y) ≤ j from not_lt.1 h)))
    have hcard : (Finset.univ.filter fun j : Fin y => j.val < i).card = i := by
      rw [Fin.card_filter_val_lt]
      omega
    simp only [e, Finset.sum_sub_distrib]
    rw [← Finset.sum_filter (fun j : Fin y => j.val < i) fun _ => t ⟨i, hi⟩, Finset.sum_const, hcard, nsmul_eq_mul, psum]
    ring
  · refine (key 0 le_rfl).trans (le_of_eq ?_)
    rw [mul_zero, add_zero, psum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [if_pos (by omega), sub_zero, max_eq_right (ht.2 j)]

theorem psum_eq {q i : ℕ} (hi : i ≤ q) (s : Fin q → ℝ) : psum s i = ∑ a : Fin i, s (Fin.castLE hi a) := by
  exact (Fintype.sum_of_injective _ (Fin.castLE_injective hi) _ (fun j : Fin q => if j.val < i then s j else 0)
    (fun j hj => if_neg fun h => hj ⟨⟨j, h⟩, rfl⟩) fun a => (if_pos a.2).symm).symm

theorem minor_of : FrameBasis → Minor := by
  intro hB F E _ _ _ _ _ σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr' C hC
  classical
  obtain ⟨b, lam, ix, iy, h1, h2, h3, -, hb⟩ := hB F E σ hσ n J hJ fr hfr
  obtain ⟨b', lam', jx, jy, h1', h2', h3', -, hb'⟩ := hB F E σ hσ d J' hJ' fr' hfr'
  obtain ⟨m, K, hm, hK, h⟩ := diag_coords τ hfr hfr' hb hb' hC
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hf : (1 : ℝ) ≤ n.factorial := by exact_mod_cast n.factorial_pos
  set A : ℝ := n.factorial * m * K with hA
  have hA1 : 1 ≤ A := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf hm') hK
  refine ⟨A⁻¹, by positivity, fun s hs t ht x hx hsupp => ?_⟩
  obtain ⟨ha, hsz⟩ := h s t x
  have hint := ha hsupp
  have hz := sz_nonneg τ (mat (fr.a s)⁻¹ * incM F x * (mat (fr'.a t)⁻¹)ᵀ)
  set z := sz τ (mat (fr.a s)⁻¹ * incM F x * (mat (fr'.a t)⁻¹)ᵀ)
  set ξ := (b⁻¹).1 * x * (b'⁻¹).1ᵀ with hξ
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i : Fin (fr.r + 1) => psum s i.val - psum t i.val)
  have hiq : i.val ≤ fr.r := Nat.lt_succ_iff.1 i.2
  have hqn : fr.r ≤ n := by simpa using Fintype.card_le_of_embedding iy
  have hrk : ξ.rank = n := by
    rw [hξ, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (by
      rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _))]
    exact hx
  have hli : LinearIndependent E ξ.row := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, ← Matrix.rank_eq_finrank_span_row, hrk,
      Fintype.card_fin]
  let ρ : Fin i.val → Fin n := fun a => iy (Fin.castLE hiq a)
  obtain ⟨c, hc, hdet⟩ := exists_cols_det_ne_zero (ξ.submatrix ρ id)
    (hli.comp ρ (iy.injective.comp (Fin.castLE_injective hiq)))
  set M : Matrix (Fin i.val) (Fin i.val) E := (ξ.submatrix ρ id).submatrix id c with hM
  have hI : IsIntegral ℤ ((m : E) • M).det := IsIntegral.det fun a a' => hint _ _
  have hI0 : ((m : E) • M).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hm.ne')) hdet
  obtain ⟨φ, hφ⟩ := exists_one_le_emb hI hI0
  obtain ⟨w, hw⟩ := norm_emb hσ τ φ
  rw [hw, Matrix.det_smul, map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast,
    Fintype.card_fin] at hφ
  let N : Matrix (Fin i.val) (Fin i.val) ℂ := Matrix.of fun a a' =>
    (Real.exp (s (Fin.castLE hiq a)) : ℂ) * ((Real.exp (-lam' (c a') t) : ℂ) * (τ w).1 (M a a'))
  have hN : ‖N.det‖ = Real.exp (psum s i - ∑ a, lam' (c a) t) * ‖(τ w).1 M.det‖ := by
    have e1 : N.det = (∏ a, (Real.exp (s (Fin.castLE hiq a)) : ℂ)) * ((∏ a, (Real.exp (-lam' (c a) t) : ℂ)) *
        (τ w).1 M.det) := by
      rw [RingHom.map_det, ← Matrix.det_mul_row, ← Matrix.det_mul_column]
      rfl
    rw [e1, ← Complex.ofReal_prod, ← Complex.ofReal_prod, ← Real.exp_sum, ← Real.exp_sum, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (Real.exp_pos _).le, ← mul_assoc, ← Real.exp_add, psum_eq hiq, Finset.sum_neg_distrib,
      sub_eq_add_neg]
  have hent : ∀ a a', ‖N a a'‖ ≤ K * (1 + z) := by
    intro a a'
    let T : InfinitePlace F → Fin n → Fin d → ℝ := fun w k l => Real.exp (-(lam k s + lam' l t)) * ‖(τ w).1 (ξ k l)‖
    have hT : ∀ w k l, 0 ≤ T w k l := fun w k l => by positivity
    have e : ‖N a a'‖ = T w (ρ a) (c a') := by
      simp only [N, T, ρ, Matrix.of_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        (h2 _ _).2, neg_add, neg_neg, Real.exp_add, mul_assoc]
      rfl
    have l1 := Finset.single_le_sum (f := T w (ρ a)) (fun _ _ => hT _ _ _) (Finset.mem_univ (c a'))
    have l2 := Finset.single_le_sum (f := fun k => ∑ l, T w k l)
      (fun _ _ => Finset.sum_nonneg fun _ _ => hT _ _ _) (Finset.mem_univ (ρ a))
    have l3 := Finset.single_le_sum (f := fun w => ∑ k, ∑ l, T w k l)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hT _ _ _) (Finset.mem_univ w)
    have l4 : ∑ w, ∑ k, ∑ l, T w k l ≤ K * z := hsz
    linarith
  have hdle : ‖N.det‖ ≤ i.val.factorial * (K * (1 + z)) ^ i.val := by
    have := Matrix.det_le (A := N) (abv := NormedField.toAbsoluteValue ℂ) (x := K * (1 + z)) hent
    rw [Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  have hv : Real.exp (viol s t) ≤ (A * (1 + z)) ^ (n + 1) := by
    have e1 : Real.exp (viol s t) ≤ Real.exp (psum s i - ∑ a, lam' (c a) t) := by
      rw [viol, ← hi]
      exact Real.exp_le_exp.2 (by linarith [sum_lam_le_psum h1' h2' h3' ht hc])
    have hin : i.val ≤ n := hiq.trans hqn
    have e2 : (i.val.factorial : ℝ) ≤ (n.factorial : ℝ) ^ (n + 1) :=
      le_trans (by exact_mod_cast Nat.factorial_le hin) (le_self_pow₀ hf (by omega))
    have hB1 : 1 ≤ (m : ℝ) * (K * (1 + z)) :=
      one_le_mul_of_one_le_of_one_le hm' (one_le_mul_of_one_le_of_one_le hK (by linarith))
    calc _ ≤ Real.exp (psum s i - ∑ a, lam' (c a) t) * ((m : ℝ) ^ i.val * ‖(τ w).1 M.det‖) :=
          e1.trans (le_mul_of_one_le_right (Real.exp_pos _).le hφ)
      _ = (m : ℝ) ^ i.val * ‖N.det‖ := by rw [hN]; ring
      _ ≤ (m : ℝ) ^ i.val * (i.val.factorial * (K * (1 + z)) ^ i.val) := by gcongr
      _ = i.val.factorial * ((m : ℝ) * (K * (1 + z))) ^ i.val := by rw [mul_pow (m : ℝ)]; ring
      _ ≤ (n.factorial : ℝ) ^ (n + 1) * ((m : ℝ) * (K * (1 + z))) ^ (n + 1) :=
          mul_le_mul e2 (pow_le_pow_right₀ hB1 (by omega)) (by positivity) (by positivity)
      _ = _ := by rw [← mul_pow, hA]; congr 1; ring
  rw [inv_mul_le_iff₀ (by positivity)]
  refine le_of_pow_le_pow_left₀ (n := n + 1) (by omega) (by positivity) ?_
  rw [← Real.exp_nat_mul, show ((n + 1 : ℕ) : ℝ) * (viol s t / (n + 1)) = viol s t by push_cast; field_simp]
  exact hv

end PositivityTheory.ThKEst

end
