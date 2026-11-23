import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEst.LatArchPf

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mul_realAd {u : AF F} (hu : evI F u = 0) (t : ℝ) : u * realAd F t = 0 := by
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h1, zero_mul]
  · change u.2 * 0 = 0
    rw [mul_zero]

theorem emb_realAd (hF : IsTotallyReal F) (w : InfinitePlace F) (t : ℝ) :
    InfinitePlace.Completion.extensionEmbedding w (evInf F w (realAd F t)) = t := by
  have hw : w.IsReal := IsTotallyReal.isReal w
  set a := (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t) with ha
  have h1 : InfiniteAdeleRing.ringEquiv_mixedSpace F a = algebraMap ℝ _ t := by
    rw [ha, RingEquiv.apply_symm_apply]
  have h2 := congrFun (congrArg Prod.fst h1) ⟨w, hw⟩
  have h3 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (a w) = t := h2
  change InfinitePlace.Completion.extensionEmbedding w (a w) = t
  rw [← h3]
  exact (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw (a w)).symm

theorem piInf_alg {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) :
    piInf τ (algebraMap (AF F) (AE F E) a) = InfinitePlace.Completion.extensionEmbedding w (evInf F w a) := by
  change infEmb τ (evInf F w a ⊗ₜ[F] (1 : E)) = _
  rw [infEmb_tmul, map_one, mul_one]

theorem piInf_rId (hF : IsTotallyReal F) {w : InfinitePlace F} (τ : EmbOver E w) (t : ℝ) :
    piInf τ (algebraMap (AF F) (AE F E) (rId F t)) = (Real.exp t : ℝ) := by
  rw [piInf_alg, rId, map_add, map_add, map_one, map_one, emb_realAd hF]
  push_cast
  ring

theorem sz_nonneg (τ : ∀ w : InfinitePlace F, EmbOver E w) {n d : ℕ} (z : Ten F E n d) : 0 ≤ sz τ z := by
  unfold sz
  positivity

theorem sz_mul_le (τ : ∀ w : InfinitePlace F, EmbOver E w) {n d : ℕ} (y : Ten F E n d)
    (B : Matrix (Fin d) (Fin d) (AE F E)) (M : ℝ) (hB : ∀ w i j, ‖piInf (τ w) (B i j)‖ ≤ M) :
    sz τ (y * Bᵀ) ≤ d * M * sz τ y := by
  unfold sz
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h : ∀ j, ‖piInf (τ w) ((y * Bᵀ) i j)‖ ≤ M * ∑ k, ‖piInf (τ w) (y i k)‖ := fun j => by
    rw [Matrix.mul_apply, map_sum, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [map_mul, norm_mul, Matrix.transpose_apply, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB w j k) (norm_nonneg _)
  refine (Finset.sum_le_sum fun j _ => h j).trans ?_
  simp [mul_assoc]

theorem incM_mul {n : ℕ} (x y : Matrix (Fin n) (Fin n) E) : incM F (x * y) = incM F x * incM F y :=
  Matrix.map_mul

theorem incM_one {n : ℕ} : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem torus (hb : FrameBasis) (hc : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {d : ℕ}
    {J : Matrix (Fin d) (Fin d) E} (hJ : EpsHerm σ J) (fr : Frame σ J) (hg : fr.IsGood) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Cone fr.r, At (evI F) (mat (fr.a t) - 1) ∧
      ∀ w i j, ‖piInf (τ w) (mat (fr.a t) i j)‖ ≤ K * Real.exp (∑ j, t j) := by
  obtain ⟨b, lam, ix, iy, -, h2, h3, -, h5⟩ := hb F E σ hc d J hJ fr hg
  set P := incM F b.1 with hP
  set Q := incM F (b⁻¹).1 with hQ
  have hPQ : P * Q = 1 := by
    rw [hP, hQ, ← incM_mul, Units.mul_inv, incM_one]
  refine ⟨∑ w, ∑ i, ∑ j, ∑ k, ‖piInf (τ w) (P i k)‖ * ‖piInf (τ w) (Q k j)‖, by positivity, fun t ht => ?_⟩
  set D : Matrix (Fin d) (Fin d) (AE F E) :=
    Matrix.diagonal fun k => algebraMap (AF F) (AE F E) (rId F (lam k t)) with hD
  have hB : mat (fr.a t) = P * D * Q := by
    rw [← h5 t, Matrix.mul_assoc, hPQ, Matrix.mul_one]
  have hlam : ∀ k, lam k t ≤ ∑ j, t j := fun k => by
    have h0 : 0 ≤ ∑ j, t j := Finset.sum_nonneg fun j _ => ht.2 j
    by_cases hk : ∀ i, ix i ≠ k ∧ iy i ≠ k
    · rw [h3 k hk]
      exact h0
    · obtain ⟨i, hi⟩ := not_forall.1 hk
      rcases not_and_or.1 hi with e | e
      · rw [← not_not.1 e, (h2 i t).1]
        exact Finset.single_le_sum (fun j _ => ht.2 j) (Finset.mem_univ i)
      · rw [← not_not.1 e, (h2 i t).2]
        exact (neg_nonpos.2 (ht.2 i)).trans h0
  refine ⟨fun u hu => ?_, fun w i j => ?_⟩
  · have hu' : u • (D - 1) = 0 := by
      ext k l
      by_cases e : k = l
      · subst e
        simp only [hD, Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
          Matrix.zero_apply, rId, map_add, map_one, add_sub_cancel_left]
        rw [Algebra.smul_def, ← map_mul, mul_realAd hu, map_zero]
      · simp [hD, Matrix.diagonal_apply_ne _ e, Matrix.one_apply_ne e]
    have e : mat (fr.a t) - 1 = P * (D - 1) * Q := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ, hB]
    rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, hu', Matrix.mul_zero, Matrix.zero_mul]
  · have h1 : ‖piInf (τ w) (mat (fr.a t) i j)‖ ≤
        (∑ k, ‖piInf (τ w) (P i k)‖ * ‖piInf (τ w) (Q k j)‖) * Real.exp (∑ j, t j) := by
      rw [hB, Matrix.mul_apply, map_sum, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [hD, Matrix.mul_diagonal, map_mul, map_mul, piInf_rId hc.1, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le, mul_right_comm]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hlam k)) (by positivity)
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    refine le_trans ?_ (Finset.single_le_sum (f := fun w => ∑ i, ∑ j, ∑ k,
      ‖piInf (τ w) (P i k)‖ * ‖piInf (τ w) (Q k j)‖) (fun _ _ => by positivity) (Finset.mem_univ w))
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ∑ k,
      ‖piInf (τ w) (P i k)‖ * ‖piInf (τ w) (Q k j)‖) (fun _ _ => by positivity) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ∑ k,
      ‖piInf (τ w) (P i k)‖ * ‖piInf (τ w) (Q k j)‖) (fun _ _ => by positivity) (Finset.mem_univ j)

theorem maj_le (τ : ∀ w : InfinitePlace F, EmbOver E w) {n d : ℕ} (C : Set (Ten F E n d)) (N : ℕ) (y : Ten F E n d)
    (B : Matrix (Fin d) (Fin d) (AE F E)) (K s : ℝ) (hK : 0 ≤ K) (hs : 1 ≤ s) (h1 : At (evI F) (B - 1))
    (hB : ∀ w i j, ‖piInf (τ w) (B i j)‖ ≤ K * s) :
    maj τ C N y ≤ ((1 + d * K) * s) ^ N * maj τ C N (y * Bᵀ) := by
  have hy := sz_nonneg τ y
  have hz := sz_nonneg τ (y * Bᵀ)
  have hs0 : 0 < s := by linarith
  unfold maj
  split_ifs with h2 h3 h3
  · have h4 := sz_mul_le τ y B _ hB
    have h5 : 1 + sz τ (y * Bᵀ) ≤ (1 + d * K) * s * (1 + sz τ y) := by
      have : 0 ≤ d * K * s := by positivity
      have : 0 ≤ s * sz τ y := by positivity
      nlinarith
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h5 N
  · refine absurd ?_ h3
    obtain ⟨c, hc, h⟩ := h2
    refine ⟨c, hc, fun u hu => ?_⟩
    have e : y * Bᵀ - c = (y - c) + y * (B - 1)ᵀ := by
      rw [Matrix.transpose_sub, Matrix.mul_sub, Matrix.transpose_one, Matrix.mul_one]
      abel
    rw [e, smul_add, h u hu, zero_add, ← Matrix.mul_smul, ← Matrix.transpose_smul, h1 u hu, Matrix.transpose_zero,
      Matrix.mul_zero]
  · positivity
  · simp

end PositivityTheory.ThKEst.LatArchPf

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK LatArchPf

theorem latArch_of (hb : FrameBasis) : LatArch := by
  intro F E _ _ _ _ _ σ hc τ n d J J' _ hJ' fr hg C N hC
  obtain ⟨K, hK, h⟩ := torus hb hc τ hJ' fr hg
  refine ⟨C, Real.toNNReal ((1 + d * K) ^ N), hC, fun S g t ht => ?_⟩
  obtain ⟨h1, h2⟩ := h t ht
  unfold latSum
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  have h0 : 0 ≤ ∑ j, t j := Finset.sum_nonneg fun j _ => ht.2 j
  have h3 := maj_le τ C N (mat g⁻¹ * incM F x.1 * (mat (fr.a t)⁻¹)ᵀ) (mat (fr.a t)) K _ hK (Real.one_le_exp h0) h1 h2
  have e : mat (fr.a t) * mat (fr.a t)⁻¹ = mat (1 : UA σ J')⁻¹ := by
    rw [inv_one, ← mul_inv_cancel (fr.a t)]
    rfl
  rw [Matrix.mul_assoc _ _ (mat (fr.a t))ᵀ, ← Matrix.transpose_mul, e] at h3
  change _ ≤ ENNReal.ofReal ((1 + d * K) ^ N) * _ * _
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (h3.trans_eq ?_)
  rw [mul_pow, Real.exp_nat_mul]

end PositivityTheory.ThKEst

end
