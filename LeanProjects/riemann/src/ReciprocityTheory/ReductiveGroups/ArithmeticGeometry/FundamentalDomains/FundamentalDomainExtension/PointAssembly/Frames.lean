import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.ZnNonneg

namespace PIW.FdPA

open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex Metric
open scoped ComplexConjugate

noncomputable section

theorem mem_dom_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x : Frame X.Ψ r) : x ∈ X.dom ↔ ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := Iff.rfl

theorem gram_eq {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = M.transpose * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

theorem det_ne_of_gram {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) (h : (gram τ G M).det ≠ 0) : M.det ≠ 0 := by
  rw [gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  intro h0
  apply h
  rw [h0, zero_mul, zero_mul]

theorem lminor_last {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) : lminor M (Fin.last r) = M.det := by
  rfl

theorem det_of_minors {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x : Frame X.Ψ r) (τ : X.Ψ) (h : ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re) :
    (mat x τ).det ≠ 0 := by
  have h1 := h (Fin.last r)
  have h2 : dmin X.Gm x τ (Fin.last r) ≠ 0 := by
    intro h0
    rw [h0] at h1
    simp at h1
  unfold dmin at h2
  rw [lminor_last] at h2
  exact det_ne_of_gram _ _ _ h2

theorem chart_zero_eq_alt {E : Type} [Field E] [NumberField E] [IsCMField E] : XZZero E := by
  intro r X x
  funext τ
  have h1 : X.lowBlock 0 τ = 1 := by
    ext a b
    simp [Data.lowBlock, Matrix.one_apply]
  simp only [Data.xZ, h1, Matrix.mul_one]
  rfl

theorem normFactor_pos_alt {E : Type} [Field E] [NumberField E] [IsCMField E] : NfacPos E := by
  intro r X la x hx
  have hx' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
  unfold Data.nfac
  refine Finset.prod_pos (fun τ _ => Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos ?_ _))
  have hne : ∀ j, dmin X.Gm x τ j ≠ 0 := by
    intro j h0
    have := (hx' τ).2 j
    rw [h0] at this
    simp at this
  exact norm_pos_iff.mpr (div_ne_zero (hne _) (hne _))

theorem unitary_domain {E : Type} [Field E] [NumberField E] [IsCMField E] : UnitDom E := by
  intro r X n x hn hx
  rw [mem_dom_iff] at hx ⊢
  intro τ

  have hcol : ∀ a, col (mat (X.lmulC n x) τ) a = Matrix.mulVec (n τ) (col (mat x τ) a) := by
    intro a
    funext k
    simp [col, mat, Data.lmulC, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rfl
  have hg : gram τ.1 X.Gm (mat (X.lmulC n x) τ) = gram τ.1 X.Gm (mat x τ) := by
    ext a b
    simp only [gram, Matrix.of_apply, hcol, hn τ]
  have hd : ∀ i, dmin X.Gm (X.lmulC n x) τ i = dmin X.Gm x τ i := by
    intro i
    simp only [dmin, hg]
  have hpos : ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (X.lmulC n x) τ i).re := by
    intro i
    rw [hd]
    exact (hx τ).2 i
  exact ⟨det_of_minors X (X.lmulC n x) τ hpos, hpos⟩

theorem orthonormal_domain {E : Type} [Field E] [NumberField E] [IsCMField E] : OrthoDom E := by
  intro r X x hx
  rw [mem_dom_iff]
  intro τ
  have hdm : ∀ i : Fin (r + 1), dmin X.Gm x τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    intro i
    simp only [dmin, lminor, hx τ]
    rw [Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    simp [psgn, Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ))]
  have hps : ∀ i : ℕ, psgn X.p0 i ≠ 0 := by
    intro i
    unfold psgn
    refine Finset.prod_ne_zero_iff.mpr (fun a _ => ?_)
    unfold sgn
    split_ifs <;> norm_num
  have hpos : ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := by
    intro i
    rw [hdm, Complex.ofReal_re]
    exact mul_self_pos.mpr (hps i)
  exact ⟨det_of_minors X x τ hpos, hpos⟩

theorem opN_smul {m n : ℕ} (t : ℂ) (A : Matrix (Fin m) (Fin n) ℂ) :
    Data.opN (t • A) = ‖t‖ * Data.opN A := by
  unfold Data.opN
  have key : ∀ v : Fin n → ℂ, √(∑ i, ‖Matrix.mulVec (t • A) v i‖ ^ 2) =
      ‖t‖ * √(∑ i, ‖Matrix.mulVec A v i‖ ^ 2) := by
    intro v
    simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  open scoped Pointwise in
  have hset : {s | ∃ v : Fin n → ℂ, v ≠ 0 ∧
        s = √(∑ i, ‖Matrix.mulVec (t • A) v i‖ ^ 2) / √(∑ j, ‖v j‖ ^ 2)} =
      ‖t‖ • {s | ∃ v : Fin n → ℂ, v ≠ 0 ∧ s = √(∑ i, ‖Matrix.mulVec A v i‖ ^ 2) / √(∑ j, ‖v j‖ ^ 2)} := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨_, ⟨v, hv, rfl⟩, by rw [key, mul_div_assoc]⟩
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, by rw [key, mul_div_assoc]⟩
  open scoped Pointwise in
  rw [hset, Real.sSup_smul_of_nonneg (norm_nonneg t), smul_eq_mul]

theorem chartNorm_smul {E : Type} [Field E] [NumberField E] [IsCMField E] : ZnSmul E := by
  intro r X t Z
  unfold Data.zN
  have h : ∀ τ, Data.opN (Matrix.of ((t • Z) τ)) = ‖t‖ * Data.opN (Matrix.of (Z τ)) := by
    intro τ
    rw [← opN_smul]
    rfl
  simp only [h]
  rw [Real.mul_iSup_of_nonneg (norm_nonneg t)]

theorem chartNorm_nonneg {E : Type} [Field E] [NumberField E] [IsCMField E] : ZnNonneg E := by
  intro r X Z
  unfold Data.zN
  refine Real.iSup_nonneg (fun τ => ?_)
  unfold Data.opN
  refine Real.sSup_nonneg (fun t ht => ?_)
  obtain ⟨v, _, rfl⟩ := ht
  positivity

theorem borel_flag_translate {E : Type} [Field E] [NumberField E] [IsCMField E] : BorFlag E := by
  classical
  intro r X x b hb hxb τ
  rw [mem_dom_iff] at hxb
  have hdet : (mat (rmul x b) τ).det ≠ 0 := (hxb τ).1
  have hdx : (mat x τ).det ≠ 0 := by
    intro h0
    apply hdet
    rw [show mat (rmul x b) τ = mat x τ * mat b τ from rfl, Matrix.det_mul, h0, zero_mul]

  have hcol : ∀ a, col (mat (rmul x b) τ) a = ∑ c, b τ c a • col (mat x τ) c := by
    intro a
    funext k
    simp [col, mat, rmul, Matrix.mul_apply, Finset.sum_apply, mul_comm]
    rfl
  have hli : ∀ y : Matrix (Fin r) (Fin r) ℂ, y.det ≠ 0 →
      LinearIndependent ℂ (fun a : Fin X.p0 => col y (Fin.castLE X.p0_le a)) := by
    intro y hy
    have h1 := Matrix.linearIndependent_cols_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det y).mpr (isUnit_iff_ne_zero.mpr hy))
    exact h1.comp (Fin.castLE X.p0_le) (Fin.castLE_injective _)
  have hle : Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat (rmul x b) τ) (Fin.castLE X.p0_le a)) ≤
      Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat x τ) (Fin.castLE X.p0_le a)) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    simp only [hcol]
    refine Submodule.sum_mem _ (fun c _ => ?_)
    by_cases hc : (c : ℕ) < X.p0
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨c, hc⟩, rfl⟩)
    · have ha := a.isLt
      have hz : b τ c (Fin.castLE X.p0_le a) = 0 :=
        (hb τ).2 c (Fin.castLE X.p0_le a) (by rw [Fin.lt_iff_val_lt_val, Fin.coe_castLE]; omega)
      rw [hz, zero_smul]
      exact Submodule.zero_mem _
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [finrank_span_eq_card (hli _ hdet), finrank_span_eq_card (hli _ hdx)]

end

end PIW.FdPA
