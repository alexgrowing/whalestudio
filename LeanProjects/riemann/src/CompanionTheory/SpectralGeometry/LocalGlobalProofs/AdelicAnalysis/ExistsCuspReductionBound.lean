import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.SmallPair

theorem exists_realBasis {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F)
    (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) :
    ∃ (κ : Type) (_ : Fintype κ) (b : Module.Basis κ ℝ (InfinitePlace F → ℝ)),
      ∀ i, ∃ a : 𝓞 F, ∀ w, b i w = ρ w (a : F) := by
  classical
  have hc : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mpr w.2 (hF.isReal w.1)⟩
  let e : mixedEmbedding.mixedSpace F ≃ₗ[ℝ] (InfinitePlace F → ℝ) :=
    { toFun := fun z w => z.1 ⟨w, hF.isReal w⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun v => (fun w => v w.1, fun w => (hc.false w).elim)
      left_inv := fun z => by
        refine Prod.ext rfl ?_
        funext w
        exact (hc.false w).elim
      right_inv := fun v => rfl }
  refine ⟨_, inferInstance, (mixedEmbedding.latticeBasis F).map e, fun i =>
    ⟨RingOfIntegers.basis F i, fun w => ?_⟩⟩
  have h1 : ((mixedEmbedding.latticeBasis F).map e) i w
      = InfinitePlace.embedding_of_isReal (hF.isReal w) (integralBasis F i) := by
    rw [Module.Basis.map_apply, mixedEmbedding.latticeBasis_apply]
    exact mixedEmbedding.mixedEmbedding_apply_isReal F _ ⟨w, hF.isReal w⟩
  rw [h1, integralBasis_apply]
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, hρ]

noncomputable def block (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![√τ.im, 0; τ.re / √τ.im, 1 / √τ.im]

theorem det_block (τ : ℂ) (h : 0 < τ.im) : (block τ).det = 1 := by
  have : √τ.im ≠ 0 := (Real.sqrt_pos.mpr h).ne'
  simp [block, det_fin_two]
  field_simp

noncomputable def bigM {ι : Type} [Fintype ι] [DecidableEq ι] (τ : ι → ℂ) :
    Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ :=
  blockDiagonal fun w => block (τ w)

theorem bigM_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] (τ : ι → ℂ)
    (v : Fin 2 × ι → ℝ) (k : Fin 2) (w : ι) :
    (bigM τ *ᵥ v) (k, w) = ∑ j, block (τ w) k j * v (j, w) := by
  simp only [bigM, mulVec, dotProduct, Fintype.sum_prod_type, blockDiagonal_apply]
  rw [Finset.sum_comm]
  simp

theorem det_bigM {ι : Type} [Fintype ι] [DecidableEq ι] (τ : ι → ℂ)
    (h : ∀ w, 0 < (τ w).im) : (bigM τ).det = 1 := by
  simp [bigM, det_blockDiagonal, det_block _ (h _)]

theorem exists_small {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type} [Fintype κ]
    [Nonempty ι]
    (b : Module.Basis κ ℝ (ι → ℝ)) (S : AddSubgroup (ι → ℝ)) (hS : ∀ i, b i ∈ S) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ τ : ι → ℂ, (∀ w, 0 < (τ w).im) →
      ∃ u ∈ S, ∃ v ∈ S, (u ≠ 0 ∨ v ≠ 0) ∧ ∀ w,
        |√(τ w).im * u w| ≤ R ∧ |(τ w).re / √(τ w).im * u w + 1 / √(τ w).im * v w| ≤ R := by
  classical
  let b₂ : Module.Basis ((_ : Fin 2) × κ) ℝ (Fin 2 × ι → ℝ) :=
    (Pi.basis fun _ : Fin 2 => b).map (LinearEquiv.curry ℝ ℝ (Fin 2) ι).symm
  have hb₂ : ∀ (ji : (_ : Fin 2) × κ) (k : Fin 2) (w : ι),
      b₂ ji (k, w) = (Pi.single ji.1 (b ji.2) : Fin 2 → ι → ℝ) k w := by
    intro ji k w
    simp [b₂, Module.Basis.map_apply, Pi.basis_apply]
  have hfund := ZSpan.isAddFundamentalDomain' b₂ (volume : Measure (Fin 2 × ι → ℝ))
  have hfin : volume (ZSpan.fundamentalDomain b₂) ≠ ∞ :=
    (ZSpan.fundamentalDomain_isBounded b₂).measure_lt_top.ne
  set V : ℝ := (volume (ZSpan.fundamentalDomain b₂)).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hproj : ∀ z ∈ Submodule.span ℤ (Set.range b₂), ∀ k : Fin 2,
      (fun w => z (k, w)) ∈ S := by
    intro z hz k
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ji, rfl⟩ := hx
      by_cases hk : k = ji.1
      · subst hk
        have : (fun w => b₂ ji (ji.1, w)) = b ji.2 := by
          funext w; simp [hb₂]
        rw [this]; exact hS _
      · have : (fun w => b₂ ji (k, w)) = 0 := by
          funext w; simp [hb₂, Pi.single_eq_of_ne hk]
        rw [this]; exact S.zero_mem
    | zero => exact S.zero_mem
    | add x y _ _ hx hy => exact S.add_mem hx hy
    | smul a x _ hx =>
      have : (fun w => (a • x) (k, w)) = a • (fun w => x (k, w)) := by
        funext w; simp
      rw [this]; exact S.zsmul_mem hx a
  refine ⟨V + 1, by positivity, fun τ hτ => ?_⟩
  let f : (Fin 2 × ι → ℝ) →ₗ[ℝ] (Fin 2 × ι → ℝ) := Matrix.toLin' (bigM τ)
  have hdet : LinearMap.det f = 1 := by
    simp only [f, LinearMap.det_toLin', det_bigM τ hτ]
  let s : Set (Fin 2 × ι → ℝ) := f ⁻¹' Metric.closedBall 0 (V + 1)
  have hsymm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    simpa [s, map_neg] using hx
  have hconv : Convex ℝ s := (convex_closedBall _ _).linear_preimage f
  have hcard : 1 ≤ Fintype.card (Fin 2 × ι) := Fintype.card_pos
  have hvol : volume (ZSpan.fundamentalDomain b₂) * 2 ^ Module.finrank ℝ (Fin 2 × ι → ℝ)
      < volume s := by
    rw [Measure.addHaar_preimage_linearMap _ (by rw [hdet]; exact one_ne_zero),
      hdet, Real.volume_pi_closedBall _ (by positivity), Module.finrank_fintype_fun_eq_card]
    have h1 : volume (ZSpan.fundamentalDomain b₂) = ENNReal.ofReal V :=
      (ENNReal.ofReal_toReal hfin).symm
    rw [h1]
    simp only [inv_one, abs_one, ENNReal.ofReal_one, one_mul]
    have h2 : (2 : ℝ≥0∞) ^ Fintype.card (Fin 2 × ι)
        = ENNReal.ofReal (2 ^ Fintype.card (Fin 2 × ι)) := by
      rw [ENNReal.ofReal_pow (by norm_num)]; simp
    rw [h2, ← ENNReal.ofReal_mul hV0]
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    rw [mul_pow, mul_comm]
    have h3 : V < (V + 1) ^ Fintype.card (Fin 2 × ι) :=
      calc V < V + 1 := by linarith
        _ = (V + 1) ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ (by linarith) hcard
    exact mul_lt_mul_of_pos_left h3 (by positivity)
  have hcount : Countable (Submodule.span ℤ (Set.range b₂)).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range b₂))
    infer_instance
  obtain ⟨⟨x, hx⟩, hne, hmem⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hfund hsymm hconv hvol
  have hx' : x ∈ Submodule.span ℤ (Set.range b₂) := hx
  refine ⟨_, hproj x hx' 0, _, hproj x hx' 1, ?_, fun w => ?_⟩
  · by_contra hcon
    push_neg at hcon
    apply hne
    apply Subtype.ext
    funext ⟨k, w⟩
    fin_cases k
    · exact congrFun hcon.1 w
    · exact congrFun hcon.2 w
  · have hball : ‖f x‖ ≤ V + 1 := by
      simpa [s] using hmem
    have hco : ∀ k, |f x (k, w)| ≤ V + 1 := fun k => by
      have := (pi_norm_le_iff_of_nonneg (by positivity)).mp hball (k, w)
      simpa using this
    have e : ∀ k, f x (k, w) = ∑ j, block (τ w) k j * x (j, w) := fun k => by
      simp only [f, Matrix.toLin'_apply]
      exact bigM_mulVec τ x k w
    have h0 := hco 0
    have h1 := hco 1
    rw [e] at h0 h1
    simpa [block, Fin.sum_univ_two] using And.intro h0 h1

theorem exists_small_pair : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) →
    ∃ C : ℝ, ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∃ c d : 𝓞 F, (c ≠ 0 ∨ d ≠ 0) ∧
      ∀ w, ‖((ρ w (c : F) : ℝ) : ℂ) * τ w + (ρ w (d : F) : ℝ)‖ ^ 2 ≤ C * (τ w).im := by
  intro F _ _ hF ρ hρ
  classical
  obtain ⟨κ, _, b, hb⟩ := exists_realBasis hF ρ hρ
  let Φ : 𝓞 F →+ (InfinitePlace F → ℝ) :=
    { toFun := fun a w => ρ w (a : F)
      map_zero' := by funext w; simp
      map_add' := fun x y => by funext w; simp }
  obtain ⟨R, hR, H⟩ := exists_small b Φ.range (fun i => by
    obtain ⟨a, ha⟩ := hb i
    exact ⟨a, funext fun w => (ha w).symm⟩)
  refine ⟨2 * R ^ 2, fun τ hτ => ?_⟩
  obtain ⟨u, ⟨c, rfl⟩, v, ⟨d, rfl⟩, hne, hbd⟩ := H τ hτ
  refine ⟨c, d, ?_, fun w => ?_⟩
  · rcases hne with h | h
    · left; rintro rfl; exact h (map_zero Φ)
    · right; rintro rfl; exact h (map_zero Φ)
  · obtain ⟨h1, h2⟩ := hbd w
    set y := (τ w).im with hy
    set X := (τ w).re with hX
    have hy0 : 0 < y := hτ w
    have hs : 0 < √y := Real.sqrt_pos.mpr hy0
    have hss : √y * √y = y := Real.mul_self_sqrt hy0.le
    set a : ℝ := ρ w (c : F) with ha
    set e : ℝ := ρ w (d : F) with he
    have h1' : |√y * a| ≤ R := h1
    have h2' : |X / √y * a + 1 / √y * e| ≤ R := h2
    have q1 : (√y * a) ^ 2 ≤ R ^ 2 := sq_le_sq' (abs_le.mp h1').1 (abs_le.mp h1').2
    have q2 : (X / √y * a + 1 / √y * e) ^ 2 ≤ R ^ 2 :=
      sq_le_sq' (abs_le.mp h2').1 (abs_le.mp h2').2
    have r1 : y * a ^ 2 ≤ R ^ 2 := by
      have : (√y * a) ^ 2 = y * a ^ 2 := by rw [mul_pow, Real.sq_sqrt hy0.le]
      linarith
    have r2 : (X * a + e) ^ 2 ≤ R ^ 2 * y := by
      have : (X / √y * a + 1 / √y * e) ^ 2 * y = (X * a + e) ^ 2 := by
        have : X / √y * a + 1 / √y * e = (X * a + e) / √y := by field_simp
        rw [this, div_pow, Real.sq_sqrt hy0.le]
        field_simp
      rw [← this]
      exact mul_le_mul_of_nonneg_right q2 hy0.le
    have nrm : ‖((a : ℝ) : ℂ) * τ w + (e : ℝ)‖ ^ 2 = (a * X + e) ^ 2 + (a * y) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [hX, hy]
      ring
    rw [nrm]
    have r3 : (a * y) ^ 2 ≤ R ^ 2 * y := by
      have : (a * y) ^ 2 = (y * a ^ 2) * y := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right r1 hy0.le
    have r4 : (a * X + e) ^ 2 = (X * a + e) ^ 2 := by ring
    rw [r4]
    nlinarith

end GlobalTheory.CompanionTheory.SW.SmallPair
