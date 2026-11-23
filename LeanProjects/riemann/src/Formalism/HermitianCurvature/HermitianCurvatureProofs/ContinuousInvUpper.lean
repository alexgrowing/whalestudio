import Formalism.HermitianCurvature.StatementG

open Matrix MeasureTheory

set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.G5

open Formalism.FourierDecayAlt.G

instance sigmaFinite_mu (β : ℂ) : SigmaFinite (mu β) := by unfold mu; infer_instance

instance sigmaFinite_muPi (β : ℂ) (ι : Type) [Fintype ι] : SigmaFinite (muPi β ι) := by
  unfold muPi; infer_instance

theorem muPi_eq (β : ℂ) (ι : Type) [Fintype ι] :
    muPi β ι = (Real.toNNReal (‖β‖ / (2 * Real.pi))) ^ Fintype.card ι • (volume : Measure (ι → ℂ)) := by
  unfold muPi
  refine Measure.pi_eq fun s hs => ?_
  simp only [mu, Measure.smul_apply, volume_pi_pi, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

theorem map_mulVec_volume {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (h : ‖M.det‖ = 1) :
    Measure.map (fun x : ι → ℂ => M *ᵥ x) volume = volume := by
  have hdet : LinearMap.det ((Matrix.toLin' M).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq, h, one_pow]
  have h2 := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ι → ℂ))
    (f := (Matrix.toLin' M).restrictScalars ℝ) (by rw [hdet]; exact one_ne_zero)
  rw [hdet] at h2
  have h3 : Measure.map (fun x : ι → ℂ => M *ᵥ x) volume = ENNReal.ofReal |(1 : ℝ)⁻¹| • volume := h2
  simpa using h3

theorem mp_mulVec (β : ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (h : ‖M.det‖ = 1) :
    MeasurePreserving (fun x : ι → ℂ => M *ᵥ x) (muPi β ι) (muPi β ι) := by
  have hm : Measurable (fun x : ι → ℂ => M *ᵥ x) := (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  refine ⟨hm, ?_⟩
  rw [muPi_eq, Measure.map_smul, map_mulVec_volume M h]

theorem mp_vecMul (β : ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (h : ‖M.det‖ = 1) :
    MeasurePreserving (fun x : ι → ℂ => x ᵥ* M) (muPi β ι) (muPi β ι) := by
  have := mp_mulVec β Mᵀ (by rwa [Matrix.det_transpose])
  simpa only [Matrix.mulVec_transpose] using this

theorem mp_add_const (β : ℂ) {ι : Type} [Fintype ι] (c : ι → ℂ) :
    MeasurePreserving (fun x : ι → ℂ => x + c) (muPi β ι) (muPi β ι) := by
  refine ⟨measurable_add_const c, ?_⟩
  rw [muPi_eq, Measure.map_smul, map_add_right_eq_self]

theorem map_smul_muPi (β z : ℂ) (ι : Type) [Fintype ι] (hz : z ≠ 0) :
    Measure.map (fun v : ι → ℂ => z • v) (muPi β ι) =
      Real.toNNReal ((‖z‖ ^ (2 * Fintype.card ι))⁻¹) • muPi β ι := by
  classical
  have hdet : LinearMap.det ((z • (LinearMap.id : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))).restrictScalars ℝ) =
      ‖z‖ ^ (2 * Fintype.card ι) := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_smul, LinearMap.det_id, mul_one,
      Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, norm_pow, ← pow_mul, mul_comm]
    simp
  have hpos : (0 : ℝ) < ‖z‖ ^ (2 * Fintype.card ι) := by positivity
  have h2 := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ι → ℂ))
    (f := (z • (LinearMap.id : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))).restrictScalars ℝ) (by rw [hdet]; exact hpos.ne')
  rw [hdet, abs_of_pos (inv_pos.2 hpos)] at h2
  have h3 : Measure.map (fun v : ι → ℂ => z • v) volume =
      ENNReal.ofReal ((‖z‖ ^ (2 * Fintype.card ι))⁻¹) • volume := h2
  rw [muPi_eq, Measure.map_smul, h3, smul_comm]
  rfl

theorem wMat_mul_self (d : ℕ) : wMat d * wMat d = 1 := by
  ext i j
  have key : ∀ k : Fin d, (if k = i.rev then (1:ℂ) else 0) * (if j = k.rev then (1:ℂ) else 0) =
      if k = i.rev then (if i = j then 1 else 0) else 0 := by
    intro k
    by_cases hk : k = i.rev
    · simp [hk, eq_comm]
    · simp [hk]
  simp only [wMat, Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply, key]
  simp

theorem norm_det_wMat (d : ℕ) : ‖(wMat d).det‖ = 1 := by
  have h := congrArg (fun M => ‖Matrix.det M‖) (wMat_mul_self d)
  simp only [Matrix.det_mul, norm_mul, Matrix.det_one, norm_one] at h
  nlinarith [norm_nonneg (wMat d).det]

theorem det_upper {d : ℕ} (v : UT d → ℂ) : (upper v).det = 1 := by
  have h : (upper v).BlockTriangular id := by
    intro i j hij
    have hij' : j < i := hij
    simp [upper, strictUpper, hij'.ne', not_lt.2 hij'.le]
  rw [Matrix.det_of_isUpperTriangular h]
  simp [upper, strictUpper]

theorem continuous_upper (d : ℕ) : Continuous (upper : (UT d → ℂ) → Matrix (Fin d) (Fin d) ℂ) := by
  refine continuous_matrix fun i j => ?_
  simp only [upper, strictUpper, Matrix.add_apply, Matrix.of_apply]
  refine continuous_const.add ?_
  split_ifs with h
  · exact continuous_apply _
  · exact continuous_const

theorem card_UT (n : ℕ) : Fintype.card (UT n) = ∑ i ∈ Finset.range n, i := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right]
  simp_rw [← Finset.card_filter]
  have : ∀ y : Fin n, (Finset.univ.filter (fun x : Fin n => x < y)).card = (y : ℕ) := by
    intro y
    rw [show Finset.univ.filter (fun x : Fin n => x < y) = Finset.Iio y by ext; simp]
    exact Fin.card_Iio y
  simp_rw [this]
  exact Fin.sum_univ_eq_sum_range (fun i => i) n

theorem two_card_UT (n : ℕ) : 2 * Fintype.card (UT n) = n * (n - 1) := by
  rw [card_UT, mul_comm]; exact Finset.sum_range_id_mul_two n

theorem mp_shear (n : ℕ) (β : ℂ) :
    MeasurePreserving (fun p : BlockCoord n => ((p.1 ᵥ* (wMat n * upper p.2.1), p.2.1, p.2.2) : BlockCoord n))
      (muBlock β n) (muBlock β n) := by
  have hm : Measurable (Function.uncurry fun (q : (UT n → ℂ) × (Fin n → ℂ)) (a : Fin n → ℂ) =>
      a ᵥ* (wMat n * upper q.1)) := by
    refine Continuous.measurable ?_
    exact Continuous.matrix_vecMul continuous_snd
      (continuous_const.matrix_mul ((continuous_upper n).comp (continuous_fst.comp continuous_fst)))
  have h1 := (MeasurePreserving.id ((muPi β (UT n)).prod (muPi β (Fin n)))).skew_product
    (μc := muPi β (Fin n)) (μd := muPi β (Fin n)) hm
    (Filter.Eventually.of_forall fun q => (mp_vecMul β (wMat n * upper q.1)
      (by rw [Matrix.det_mul, det_upper, mul_one, norm_det_wMat])).map_eq)
  exact (Measure.measurePreserving_swap.comp h1).comp Measure.measurePreserving_swap

theorem symm_castSucc {n : ℕ} (i : Fin n) :
    finSumFinEquiv.symm (i.castSucc : Fin (n + 1)) = Sum.inl i :=
  finSumFinEquiv_symm_apply_castAdd (n := 1) i

theorem symm_last (n : ℕ) : finSumFinEquiv.symm (Fin.last n : Fin (n + 1)) = Sum.inr (0 : Fin 1) :=
  finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)

theorem blk_cc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i j : Fin n) :
    blk A b a e i.castSucc j.castSucc = A i j := by
  simp [blk, symm_castSucc]

theorem blk_cl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i : Fin n) :
    blk A b a e i.castSucc (Fin.last n) = b i := by
  simp [blk, symm_castSucc, symm_last]

theorem blk_lc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (j : Fin n) :
    blk A b a e (Fin.last n) j.castSucc = a j := by
  simp [blk, symm_castSucc, symm_last]

theorem blk_ll {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) :
    blk A b a e (Fin.last n) (Fin.last n) = e := by
  simp [blk, symm_last]

theorem blk_mul {n : ℕ} (A A' : Matrix (Fin n) (Fin n) ℂ) (b a b' a' : Fin n → ℂ) (e e' : ℂ) :
    blk A b a e * blk A' b' a' e' =
      blk (A * A' + Matrix.vecMulVec b a') (A *ᵥ b' + e' • b) (a ᵥ* A' + e • a') (a ⬝ᵥ b' + e * e') := by
  unfold blk
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply]
  congr 2
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
  · ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · ext i j; simp [Matrix.mul_apply, dotProduct]

theorem blk_mul_upper {n : ℕ} (A A' : Matrix (Fin n) (Fin n) ℂ) (b b' : Fin n → ℂ) :
    blk A b 0 1 * blk A' b' 0 1 = blk (A * A') (A *ᵥ b' + b) 0 1 := by
  rw [blk_mul]; simp

theorem lowRow_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ) :
    lowRow a * blk A 0 0 1 = blk A 0 (a ᵥ* A) 1 := by
  unfold lowRow
  rw [blk_mul]; simp

theorem blk_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) :
    (blk A b a e)ᵀ = blk Aᵀ a b e := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.transpose_apply, blk_cc, blk_cl, blk_lc, blk_ll]

theorem blk_one (n : ℕ) : blk (1 : Matrix (Fin n) (Fin n) ℂ) 0 0 1 = 1 := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [blk_cc, blk_cl, blk_lc, blk_ll, Matrix.one_apply, Fin.ext_iff, ne_of_gt, ne_of_lt]

theorem upper_mul_inv {d : ℕ} (v : UT d → ℂ) : upper v * (upper v)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (by rw [det_upper]; exact isUnit_one)

theorem inv_blk {n : ℕ} (v : UT n → ℂ) (b : Fin n → ℂ) :
    (blk (upper v) b 0 1)⁻¹ = blk (upper v)⁻¹ ((-(upper v)⁻¹) *ᵥ b) 0 1 := by
  refine Matrix.inv_eq_right_inv ?_
  rw [blk_mul_upper, upper_mul_inv, Matrix.mulVec_mulVec, Matrix.mul_neg, upper_mul_inv, Matrix.neg_mulVec,
    Matrix.one_mulVec, neg_add_cancel, blk_one]

theorem det_inv_upper {d : ℕ} (v : UT d → ℂ) : ((upper v)⁻¹).det = 1 := by
  rw [Matrix.det_nonsing_inv, det_upper, Ring.inverse_one]

theorem continuous_inv_upper (d : ℕ) : Continuous (fun v : UT d → ℂ => (upper v)⁻¹) := by
  have h : (fun v : UT d → ℂ => (upper v)⁻¹) = fun v => (upper v).adjugate := by
    funext v
    rw [Matrix.inv_def, det_upper, Ring.inverse_one, one_smul]
  rw [h]
  exact (continuous_upper d).matrix_adjugate

theorem continuous_coordU (d : ℕ) : Continuous (coordU : Matrix (Fin d) (Fin d) ℂ → UT d → ℂ) :=
  continuous_pi fun p => continuous_id.matrix_elem p.1.1 p.1.2

theorem coordU_upper {d : ℕ} (v : UT d → ℂ) : coordU (upper v) = v := by
  funext p
  obtain ⟨⟨i, j⟩, h⟩ := p
  have h' : i < j := h
  simp [coordU, upper, strictUpper, h', h'.ne]

noncomputable def idxEquiv (n : ℕ) : UT n ⊕ Fin n ≃ UT (n + 1) :=
  Equiv.ofBijective
    (Sum.elim (fun p => ⟨(p.1.1.castSucc, p.1.2.castSucc), Fin.castSucc_lt_castSucc_iff.2 p.2⟩)
      (fun i => ⟨(i.castSucc, Fin.last n), Fin.castSucc_lt_last i⟩))
    (by
      constructor
      · rintro (⟨⟨i, j⟩, h⟩ | i) (⟨⟨i', j'⟩, h'⟩ | i') hh
        · simp only [Sum.elim_inl, Subtype.mk.injEq, Prod.mk.injEq, Fin.castSucc_inj] at hh
          simp [hh.1, hh.2]
        · simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq, Prod.mk.injEq] at hh
          exact absurd hh.2 (Fin.castSucc_lt_last j).ne
        · simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq, Prod.mk.injEq] at hh
          exact absurd hh.2.symm (Fin.castSucc_lt_last j').ne
        · simp only [Sum.elim_inr, Subtype.mk.injEq, Prod.mk.injEq, Fin.castSucc_inj, and_true] at hh
          rw [hh]
      · rintro ⟨⟨i, j⟩, h⟩
        have h' : i < j := h
        induction j using Fin.lastCases with
        | last =>
          induction i using Fin.lastCases with
          | last => exact absurd h' (lt_irrefl _)
          | cast i => exact ⟨Sum.inr i, rfl⟩
        | cast j =>
          induction i using Fin.lastCases with
          | last => exact absurd h' (not_lt.2 (Fin.castSucc_lt_last j).le)
          | cast i => exact ⟨Sum.inl ⟨(i, j), Fin.castSucc_lt_castSucc_iff.1 h'⟩, rfl⟩)

noncomputable def joinU {n : ℕ} (q : (UT n → ℂ) × (Fin n → ℂ)) : UT (n + 1) → ℂ :=
  fun p => Sum.elim q.1 q.2 ((idxEquiv n).symm p)

theorem joinU_idx {n : ℕ} (q : (UT n → ℂ) × (Fin n → ℂ)) (s : UT n ⊕ Fin n) :
    joinU q (idxEquiv n s) = Sum.elim q.1 q.2 s := by
  simp [joinU]

theorem coordU_blk {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) :
    coordU (blk A b a e) = joinU (coordU A, b) := by
  funext p
  obtain ⟨s, rfl⟩ := (idxEquiv n).surjective p
  rw [joinU_idx]
  rcases s with ⟨⟨i, j⟩, h⟩ | i
  · exact blk_cc A b a e i j
  · exact blk_cl A b a e i

theorem joinU_surjective (n : ℕ) : Function.Surjective (joinU : (UT n → ℂ) × (Fin n → ℂ) → UT (n + 1) → ℂ) := by
  intro k
  refine ⟨(fun p => k (idxEquiv n (Sum.inl p)), fun i => k (idxEquiv n (Sum.inr i))), ?_⟩
  funext p
  obtain ⟨s, rfl⟩ := (idxEquiv n).surjective p
  rw [joinU_idx]
  rcases s with p | i <;> rfl

theorem upper_joinU {n : ℕ} (v : UT n → ℂ) (b : Fin n → ℂ) : upper (joinU (v, b)) = blk (upper v) b 0 1 := by
  have hj : joinU (v, b) = coordU (blk (upper v) b 0 1) := by rw [coordU_blk, coordU_upper]
  rw [hj]
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [upper, strictUpper, blk_ll]
    | cast j =>
      have h1 : ¬ (Fin.last n < j.castSucc) := not_lt.2 (Fin.castSucc_lt_last j).le
      simp [upper, strictUpper, blk_lc, h1, (Fin.castSucc_lt_last j).ne']
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [upper, strictUpper, coordU, blk_cl, Fin.castSucc_lt_last, (Fin.castSucc_lt_last i).ne]
    | cast j =>
      by_cases h : i < j
      · simp [upper, strictUpper, coordU, blk_cc, h, h.ne]
      · simp [upper, strictUpper, coordU, blk_cc, h, Matrix.one_apply]

theorem mp_comp_equiv (β : ℂ) {ι ι' : Type} [Fintype ι] [Fintype ι'] (σ : ι ≃ ι') :
    MeasurePreserving (fun v : ι' → ℂ => v ∘ σ) (muPi β ι') (muPi β ι) := by
  have h := measurePreserving_piCongrLeft (α := fun _ : ι => ℂ) (fun _ : ι => mu β) σ.symm
  have he : (fun v : ι' → ℂ => v ∘ σ) = MeasurableEquiv.piCongrLeft (fun _ : ι => ℂ) σ.symm := by
    funext v i
    obtain ⟨j, rfl⟩ := σ.symm.surjective i
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    simp
  rw [he]
  exact h

theorem mp_joinU (β : ℂ) (n : ℕ) :
    MeasurePreserving (joinU : (UT n → ℂ) × (Fin n → ℂ) → UT (n + 1) → ℂ)
      ((muPi β (UT n)).prod (muPi β (Fin n))) (muPi β (UT (n + 1))) := by
  have h1 := measurePreserving_sumPiEquivProdPi_symm (X := fun _ : UT n ⊕ Fin n => ℂ) (fun _ => mu β)
  have h2 := mp_comp_equiv β (idxEquiv n).symm
  have h3 := h2.comp h1
  have he : (joinU : (UT n → ℂ) × (Fin n → ℂ) → UT (n + 1) → ℂ) =
      (fun v : UT n ⊕ Fin n → ℂ => v ∘ (idxEquiv n).symm) ∘
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : UT n ⊕ Fin n => ℂ)).symm := by
    funext q p
    simp only [joinU, Function.comp]
    rcases (idxEquiv n).symm p with s | s <;> rfl
  rw [he]
  exact h3

theorem mp_of_comp {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {ν : Measure α} {μ : Measure β} {μ' : Measure γ} {J : α → β} {F : β → γ}
    (hJ : MeasurePreserving J ν μ) (hF : Measurable F) (h : MeasurePreserving (F ∘ J) ν μ') :
    MeasurePreserving F μ μ' :=
  ⟨hF, by rw [← hJ.map_eq, Measure.map_map hF hJ.measurable]; exact h.map_eq⟩

instance sigmaFinite_muBlock (β : ℂ) (n : ℕ) : SigmaFinite (muBlock β n) := by
  unfold muBlock; infer_instance

theorem mp_invU (β : ℂ) : ∀ n : ℕ,
    MeasurePreserving (fun v : UT n → ℂ => coordU (upper v)⁻¹) (muPi β (UT n)) (muPi β (UT n)) := by
  intro n
  induction n with
  | zero =>
    have h : (fun v : UT 0 → ℂ => coordU (upper v)⁻¹) = id := by
      funext v p
      exact p.1.1.elim0
    rw [h]
    exact MeasurePreserving.id _
  | succ n ih =>
    have hF : Measurable (fun v : UT (n + 1) → ℂ => coordU (upper v)⁻¹) :=
      ((continuous_coordU _).comp (continuous_inv_upper _)).measurable
    refine mp_of_comp (mp_joinU β n) hF ?_
    have hm : Measurable (Function.uncurry fun (v : UT n → ℂ) (b : Fin n → ℂ) => (-(upper v)⁻¹) *ᵥ b) := by
      refine Continuous.measurable ?_
      exact Continuous.matrix_mulVec ((continuous_inv_upper n).comp continuous_fst).neg continuous_snd
    have hS := ih.skew_product (μc := muPi β (Fin n)) (μd := muPi β (Fin n)) hm
      (Filter.Eventually.of_forall fun v => (mp_mulVec β (-(upper v)⁻¹)
        (by rw [Matrix.det_neg, det_inv_upper]; simp)).map_eq)
    have he : (fun v : UT (n + 1) → ℂ => coordU (upper v)⁻¹) ∘ joinU =
        joinU ∘ fun p : (UT n → ℂ) × (Fin n → ℂ) => (coordU (upper p.1)⁻¹, (-(upper p.1)⁻¹) *ᵥ p.2) := by
      funext p
      obtain ⟨v, b⟩ := p
      simp only [Function.comp]
      rw [upper_joinU, inv_blk, coordU_blk]
    rw [he]
    exact (mp_joinU β n).comp hS

theorem mp_lmulU (β : ℂ) : ∀ (n : ℕ) (k : UT n → ℂ),
    MeasurePreserving (fun u : UT n → ℂ => coordU (upper k * upper u)) (muPi β (UT n)) (muPi β (UT n)) := by
  intro n
  induction n with
  | zero =>
    intro k
    have h : (fun u : UT 0 → ℂ => coordU (upper k * upper u)) = id := by
      funext v p
      exact p.1.1.elim0
    rw [h]
    exact MeasurePreserving.id _
  | succ n ih =>
    intro k
    obtain ⟨⟨k0, kb⟩, rfl⟩ := joinU_surjective n k
    have hF : Measurable (fun u : UT (n + 1) → ℂ => coordU (upper (joinU (k0, kb)) * upper u)) :=
      ((continuous_coordU _).comp (continuous_const.matrix_mul (continuous_upper _))).measurable
    refine mp_of_comp (mp_joinU β n) hF ?_
    have hS := (ih k0).prod ((mp_add_const β kb).comp (mp_mulVec β (upper k0) (by rw [det_upper]; simp)))
    have he : (fun u : UT (n + 1) → ℂ => coordU (upper (joinU (k0, kb)) * upper u)) ∘ joinU =
        joinU ∘ Prod.map (fun u : UT n → ℂ => coordU (upper k0 * upper u))
          ((fun x : Fin n → ℂ => x + kb) ∘ fun x : Fin n → ℂ => upper k0 *ᵥ x) := by
      funext p
      obtain ⟨v, b⟩ := p
      simp only [Function.comp, Prod.map]
      rw [upper_joinU, upper_joinU, blk_mul_upper, coordU_blk]
    rw [he]
    exact (mp_joinU β n).comp hS

def revEquiv (n : ℕ) : UT n ≃ UT n where
  toFun p := ⟨(p.1.2.rev, p.1.1.rev), Fin.rev_lt_rev.2 p.2⟩
  invFun p := ⟨(p.1.2.rev, p.1.1.rev), Fin.rev_lt_rev.2 p.2⟩
  left_inv p := by simp
  right_inv p := by simp

theorem wMat_mul_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (wMat n * A) i j = A i.rev j := by
  simp [wMat, Matrix.mul_apply]

theorem mul_wMat_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (A * wMat n) i j = A i j.rev := by
  have h : ∀ k : Fin n, (j = k.rev) = (k = j.rev) := fun k => by
    rw [eq_iff_iff]
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp [wMat, Matrix.mul_apply, h]

theorem coordU_conj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    coordU (wMat n * A * wMat n)ᵀ = coordU A ∘ revEquiv n := by
  funext p
  simp only [coordU, Matrix.transpose_apply, mul_wMat_apply, wMat_mul_apply, Function.comp, revEquiv,
    Equiv.coe_fn_mk]

end Formalism.FourierDecayAlt.P.G5

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G5

theorem jacobian_formula : Formalism.FourierDecayAlt.G.Jacobian := by
  intro n β t ht
  have hcomp : coordMap n t = (Prod.map (fun v : Fin n → ℂ => t • v)
      (Prod.map (fun v : UT n → ℂ => t • v) (fun v : Fin n → ℂ => t • v))) ∘
      (fun p : BlockCoord n => ((p.1 ᵥ* (wMat n * upper p.2.1), p.2.1, p.2.2) : BlockCoord n)) := by
    funext p
    rfl
  have hm1 : ∀ ι : Type, Measurable (fun v : ι → ℂ => t • v) := fun ι => measurable_const_smul t
  rw [hcomp, ← Measure.map_map ((hm1 _).prodMap ((hm1 _).prodMap (hm1 _))) (mp_shear n β).measurable,
    (mp_shear n β).map_eq]
  unfold muBlock
  rw [← Measure.map_prod_map _ _ (hm1 _) ((hm1 _).prodMap (hm1 _)), ← Measure.map_prod_map _ _ (hm1 _) (hm1 _),
    map_smul_muPi β t _ ht, map_smul_muPi β t _ ht, Measure.prod_smul_left, Measure.prod_smul_left,
    Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_right, smul_smul, smul_smul]
  congr 1
  rw [← Real.toNNReal_mul (by positivity), ← Real.toNNReal_mul (by positivity), ← mul_inv, ← mul_inv,
    ← pow_add, ← pow_add, two_card_UT, Fintype.card_fin]
  congr 3
  cases n with
  | zero => rfl
  | succ k => simp only [Nat.add_sub_cancel]; ring

theorem quotient_measure : Formalism.FourierDecayAlt.G.QuotientMeasure := by
  intro n β
  have hι : MeasurePreserving (fun k : UT n → ℂ => coordU (wMat n * (upper k)⁻¹ * wMat n)ᵀ)
      (muPi β (UT n)) (muPi β (UT n)) := by
    simp only [coordU_conj]
    exact (mp_comp_equiv β (revEquiv n)).comp (mp_invU β n)
  have hm : Measurable (Function.uncurry fun (k : UT n → ℂ) (r : BlockCoord n) =>
      ((r.1 ᵥ* (wMat n * (upper k)⁻¹ * wMat n), coordU (upper k * upper r.2.1), upper k *ᵥ r.2.2) :
        BlockCoord n)) := by
    refine Continuous.measurable ?_
    have hk : Continuous fun p : (UT n → ℂ) × BlockCoord n => upper p.1 :=
      (continuous_upper n).comp continuous_fst
    have hki : Continuous fun p : (UT n → ℂ) × BlockCoord n => (upper p.1)⁻¹ :=
      (continuous_inv_upper n).comp continuous_fst
    refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
    · exact Continuous.matrix_vecMul (continuous_fst.comp continuous_snd)
        ((continuous_const.matrix_mul hki).matrix_mul continuous_const)
    · exact (continuous_coordU n).comp (hk.matrix_mul
        ((continuous_upper n).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))))
    · exact Continuous.matrix_mulVec hk (continuous_snd.comp (continuous_snd.comp continuous_snd))
  have hS := hι.skew_product (μc := muBlock β n) (μd := muBlock β n) hm
    (Filter.Eventually.of_forall fun k =>
      ((mp_vecMul β (wMat n * (upper k)⁻¹ * wMat n)
          (by rw [Matrix.det_mul, Matrix.det_mul, det_inv_upper, norm_mul, norm_mul, norm_det_wMat]; simp)).prod
        ((mp_lmulU β n k).prod (mp_mulVec β (upper k) (by rw [det_upper]; simp)))).map_eq)
  have hA := (measurePreserving_prodAssoc (muPi β (UT n)) (muPi β (Fin n))
    ((muPi β (UT n)).prod (muPi β (Fin n)))).symm
  have hJ := (mp_joinU β n).prod (mp_joinU β n)
  have hall := hJ.comp (hA.comp hS)
  have he : quotMap n = Prod.map joinU joinU ∘ (MeasurableEquiv.prodAssoc.symm ∘
      fun p : (UT n → ℂ) × BlockCoord n => (coordU (wMat n * (upper p.1)⁻¹ * wMat n)ᵀ,
        ((p.2.1 ᵥ* (wMat n * (upper p.1)⁻¹ * wMat n), coordU (upper p.1 * upper p.2.2.1),
          upper p.1 *ᵥ p.2.2.2) : BlockCoord n))) := by
    funext q
    obtain ⟨k, a, u, b⟩ := q
    simp only [quotMap, Function.comp]
    rw [lowRow_mul, blk_transpose, coordU_blk, blk_mul_upper, coordU_blk, add_zero]
    rfl
  rw [he]
  exact hall

end Formalism.FourierDecayAlt.P
