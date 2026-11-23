import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

private lemma re_mul_conj (z : ℂ) : (z * (starRingEnd ℂ) z).re = ‖z‖ ^ 2 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

private lemma sum_mul_le {ι : Type} [Fintype ι] (f g : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    ∑ i, f i * g i ≤ (∑ i, f i) * ∑ i, g i := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => hg j) (Finset.mem_univ i)) (hf i)

private lemma cs_norm {ι : Type} [Fintype ι] (f g : ι → ℂ) :
    ‖∑ i, f i * g i‖ ^ 2 ≤ (∑ i, ‖f i‖ ^ 2) * ∑ i, ‖g i‖ ^ 2 := by
  refine le_trans ?_ (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖f i‖) (fun i => ‖g i‖))
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private lemma qf_eq (w : Fin a → Cinf E) : qf w = ∑ v : InfinitePlace E, ∑ i, ‖w i v‖ ^ 2 := by
  unfold qf; exact Finset.sum_comm

private lemma trF_eq (X Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    trF X Y = (∑ p : InfinitePlace E × Fin a × Fin a, X p.2.1 p.2.2 p.1 * Y p.2.2 p.2.1 p.1).re := by
  simp [trF, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_apply]

private lemma quad_eq (w x : Fin a → Cinf E) :
    quad (vecMulVec w (star w)) x = ∑ v : InfinitePlace E, ‖(x ⬝ᵥ w) v‖ ^ 2 := by
  unfold quad
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Matrix.vecMul_vecMulVec, smul_dotProduct, ← re_mul_conj]
  congr 1
  simp [dotProduct, Finset.sum_apply, mul_comm]

end

theorem UpperTheory.traceForm_cauchy_schwarz_cmDatum :
    RankOne := by
  intro E _ _ a w
  refine ⟨?_, fun M => ?_, fun x => ⟨?_, ?_, fun h => ?_⟩⟩
  · rw [qf_eq]
    unfold trF
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Matrix.one_mul, Matrix.trace, Matrix.diag, vecMulVec_apply, Finset.sum_apply, Complex.re_sum,
      Pi.mul_apply, Pi.star_apply, Complex.star_def, re_mul_conj]
  · have hM : ∀ i j v, M.1 j i v = (starRingEnd ℂ) (M.1 i j v) := by
      intro i j v
      have h : star M.1 = M.1 := M.2
      conv_lhs => rw [← h]
      rfl
    have h1 : trF M.1 M.1 = ∑ p : InfinitePlace E × Fin a × Fin a, ‖M.1 p.2.1 p.2.2 p.1‖ ^ 2 := by
      rw [trF_eq, Complex.re_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hM p.2.1 p.2.2, re_mul_conj]
    have h2 : ∑ p : InfinitePlace E × Fin a × Fin a, ‖(vecMulVec w (star w)) p.2.2 p.2.1 p.1‖ ^ 2 ≤ qf w ^ 2 := by
      rw [qf_eq, sq (∑ v : InfinitePlace E, ∑ i, ‖w i v‖ ^ 2)]
      refine le_trans (le_of_eq ?_) (sum_mul_le _ _ (fun v => by positivity) (fun v => by positivity))
      simp only [Fintype.sum_prod_type, Finset.sum_mul_sum, vecMulVec_apply, Pi.mul_apply, Pi.star_apply,
        norm_mul, norm_star, mul_pow, mul_comm]
    rw [h1, trF_eq]
    refine le_trans ?_ ((cs_norm _ _).trans (mul_le_mul_of_nonneg_left h2 (by positivity)))
    exact sq_le_sq' (abs_le.1 (Complex.abs_re_le_norm _)).1 (abs_le.1 (Complex.abs_re_le_norm _)).2
  · rw [quad_eq]
    have hs : 0 ≤ ∑ v : InfinitePlace E, ‖(x ⬝ᵥ w) v‖ ^ 2 := by positivity
    rw [← Real.le_sqrt (norm_nonneg _) hs]
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun v => ?_
    rw [Real.le_sqrt (norm_nonneg _) hs]
    exact Finset.single_le_sum (f := fun v => ‖(x ⬝ᵥ w) v‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ v)
  · rw [quad_eq, qf_eq, qf_eq, mul_comm]
    refine le_trans ?_ (sum_mul_le _ _ (fun v => by positivity) (fun v => by positivity))
    refine Finset.sum_le_sum fun v _ => ?_
    have := cs_norm (fun i => x i v) (fun i => w i v)
    simpa [dotProduct, Finset.sum_apply] using this
  · rw [quad_eq, h]; simp
