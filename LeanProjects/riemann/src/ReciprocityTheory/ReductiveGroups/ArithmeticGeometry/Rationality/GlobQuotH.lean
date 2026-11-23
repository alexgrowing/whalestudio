import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.GlobSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Hadamard

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

lemma unzero_toAdd_eq_log (y : WithZero (Multiplicative ℤ)) (hy : y ≠ 0) :
    (WithZero.unzero hy).toAdd = WithZero.log y := by
  induction y using WithZero.recZeroCoe with
  | zero => exact absurd rfl hy
  | coe a => rfl

lemma norm_emb_eq (v : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    ‖FinitePlace.embedding v x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(ordAt v x)) := by
  have hv : v.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have h1 : Valued.v (FinitePlace.embedding v x) = v.valuation K x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  rw [FinitePlace.norm_def, h1, WithZeroMulInt.toNNReal_neg_apply _ hv, ordAt, neg_neg,
    unzero_toAdd_eq_log _ hv]
  push_cast
  rfl

lemma one_lt_absNorm_real (v : HeightOneSpectrum (𝓞 K)) : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

lemma log_norm_emb (v : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    Real.log ‖FinitePlace.embedding v x‖ = -((ordAt v x : ℝ) * logN v) := by
  rw [norm_emb_eq v hx, Real.log_zpow, logN]
  push_cast
  ring

lemma finite_mulSupport_emb {x : K} (hx : x ≠ 0) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => ‖FinitePlace.embedding v x‖).Finite := by
  have h : (Function.mulSupport fun w : FinitePlace K => w x).Finite :=
    FinitePlace.mulSupport_finite hx
  refine (h.image FinitePlace.maximalIdeal).subset ?_
  intro v hv
  refine ⟨FinitePlace.mk v, ?_, FinitePlace.maximalIdeal_mk v⟩
  simpa [Function.mem_mulSupport, FinitePlace.mk_apply] using hv

lemma support_ordAt_sub {x : K} (hx : x ≠ 0) :
    (Function.support fun v : HeightOneSpectrum (𝓞 K) => (ordAt v x : ℝ) * logN v) ⊆
      Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => ‖FinitePlace.embedding v x‖ := by
  intro v hv
  rw [Function.mem_support] at hv
  rw [Function.mem_mulSupport]
  intro h
  apply hv
  have h2 := log_norm_emb v hx
  rw [h, Real.log_one] at h2
  linarith

lemma finite_ordAt {x : K} (hx : x ≠ 0) :
    (Function.support fun v : HeightOneSpectrum (𝓞 K) => (ordAt v x : ℝ) * logN v).Finite :=
  (finite_mulSupport_emb hx).subset (support_ordAt_sub hx)

lemma finsum_ordAt {x : K} (hx : x ≠ 0) :
    ∑ᶠ v : HeightOneSpectrum (𝓞 K), (ordAt v x : ℝ) * logN v =
      ∑ σ : InfinitePlace K, (σ.mult : ℝ) * Real.log (σ x) := by
  have hfin : (Function.mulSupport fun w : FinitePlace K => w x).Finite :=
    FinitePlace.mulSupport_finite hx
  have hprod := NumberField.prod_abs_eq_one hx
  have hA : 0 < ∏ w : InfinitePlace K, w x ^ w.mult :=
    Finset.prod_pos fun w _ => pow_pos (InfinitePlace.pos_iff.2 hx) _
  set s := hfin.toFinset with hs
  have hBs : ∏ᶠ w : FinitePlace K, w x = ∏ w ∈ s, w x :=
    finprod_eq_prod_of_mulSupport_subset _ (by simp [s])
  have hB : 0 < ∏ w ∈ s, w x := Finset.prod_pos fun w _ => FinitePlace.pos_iff.2 hx
  rw [hBs] at hprod
  have hlog := congrArg Real.log hprod
  rw [Real.log_mul hA.ne' hB.ne', Real.log_one,
    Real.log_prod (fun w _ => (pow_pos (InfinitePlace.pos_iff.2 hx) _).ne'),
    Real.log_prod (fun w _ => (FinitePlace.pos_iff.2 hx).ne')] at hlog
  simp only [Real.log_pow] at hlog
  have hfs : ∑ w ∈ s, Real.log (w x) = ∑ᶠ w : FinitePlace K, Real.log (w x) := by
    rw [finsum_eq_sum_of_support_subset]
    intro w hw
    simp only [Function.mem_support] at hw
    simp only [s, Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hw
    rw [h1, Real.log_one]
  have heq : ∑ᶠ w : FinitePlace K, Real.log (w x) =
      -∑ᶠ v : HeightOneSpectrum (𝓞 K), (ordAt v x : ℝ) * logN v := by
    rw [← finsum_neg_distrib, ← finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    refine finsum_congr fun v => ?_
    have h3 : (FinitePlace.equivHeightOneSpectrum.symm v) x = ‖FinitePlace.embedding v x‖ := by
      rw [← FinitePlace.mk_apply]
      rfl
    rw [h3, log_norm_emb v hx]
  linarith

lemma log_det_le {ρ : ℕ} (m : Matrix (Fin ρ) (Fin ρ) K) (hdet : m.det ≠ 0) (σ : InfinitePlace K)
    (a b : Fin ρ → ℝ) (harch : ∀ i j, m i j ≠ 0 → Real.log (σ (m i j)) + a i ≤ b j) :
    Real.log (σ m.det) ≤ ∑ j, b j - ∑ i, a i + (ρ : ℝ) / 2 * Real.log ρ := by
  rcases Nat.eq_zero_or_pos ρ with rfl | hρ
  · simp [Matrix.det_fin_zero]
  have hpos : 0 < σ m.det := InfinitePlace.pos_iff.2 hdet
  let A : Matrix (Fin ρ) (Fin ρ) ℂ := fun i j => (Real.exp (a i) : ℂ) * σ.embedding (m i j)
  have hAdet : A.det = (∏ i, (Real.exp (a i) : ℂ)) * σ.embedding m.det := by
    have h : A = Matrix.diagonal (fun i => (Real.exp (a i) : ℂ)) * (σ.embedding.mapMatrix m) := by
      ext i j
      simp [A, Matrix.diagonal_mul]
    rw [h, Matrix.det_mul, Matrix.det_diagonal, ← RingHom.map_det]
  have hnormA : ‖A.det‖ = Real.exp (∑ i, a i) * σ m.det := by
    rw [hAdet, norm_mul, norm_prod, InfinitePlace.norm_embedding_eq, Real.exp_sum]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hentry : ∀ i j, ‖A i j‖ ≤ Real.exp (b j) := by
    intro i j
    by_cases h : m i j = 0
    · simp [A, h, (Real.exp_pos _).le]
    · have hp : 0 < σ (m i j) := InfinitePlace.pos_iff.2 h
      have h2 := harch i j h
      simp only [A, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        InfinitePlace.norm_embedding_eq]
      calc Real.exp (a i) * σ (m i j) = Real.exp (a i + Real.log (σ (m i j))) := by
            rw [Real.exp_add, Real.exp_log hp]
        _ ≤ Real.exp (b j) := Real.exp_le_exp.2 (by linarith)
  have hcol : ∀ j, Real.sqrt (∑ i, ‖A i j‖ ^ 2) ≤ Real.sqrt ρ * Real.exp (b j) := by
    intro j
    rw [← Real.sqrt_sq (Real.exp_pos (b j)).le, ← Real.sqrt_mul (Nat.cast_nonneg _)]
    apply Real.sqrt_le_sqrt
    calc ∑ i, ‖A i j‖ ^ 2 ≤ ∑ _i : Fin ρ, Real.exp (b j) ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hentry i j) 2
      _ = ρ * Real.exp (b j) ^ 2 := by simp
  have hH := ReciprocityTheory.ChartRestriction.G.T0.hadamard_det_le A.transpose
  rw [Matrix.det_transpose, hnormA] at hH
  simp only [Matrix.transpose_apply] at hH
  have hprod : ∏ j, Real.sqrt (∑ i, ‖A i j‖ ^ 2) ≤ ∏ j : Fin ρ, (Real.sqrt ρ * Real.exp (b j)) :=
    Finset.prod_le_prod (fun j _ => Real.sqrt_nonneg _) fun j _ => hcol j
  have key : Real.exp (∑ i, a i) * σ m.det ≤ Real.sqrt ρ ^ ρ * Real.exp (∑ j, b j) := by
    calc _ ≤ _ := hH
      _ ≤ _ := hprod
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Real.exp_sum]
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.2 (by exact_mod_cast hρ)
  have h1 := Real.log_le_log (mul_pos (Real.exp_pos _) hpos) key
  rw [Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp,
    Real.log_mul (pow_pos hs _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_pow,
    Real.log_sqrt (Nat.cast_nonneg _)] at h1
  linarith

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
