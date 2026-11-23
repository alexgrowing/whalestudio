import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsNeZeroNormSqLeMulCovolumeRpow

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.MinkowskiProductBounds

open Module Submodule

theorem mink {W V ι : Type} [AddCommGroup W] [Module ℝ W] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [Fintype ι] (b : Basis ι ℝ W) (e : W ≃ₗ[ℝ] V)
    (Δ ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, ∀ T : W →ₗ[ℝ] W, LinearMap.det T ≠ 0 →
      |LinearMap.det T| ≤ Δ → (∀ x ∈ span ℤ (Set.range b), x ≠ 0 → ε ≤ ‖e (T x)‖) →
      ∃ v : Basis (Fin (finrank ℝ V)) ℝ W, ∀ i, v i ∈ span ℤ (Set.range b) ∧ ‖e (T (v i))‖ ≤ C := by
  classical
  borelize V
  have : FiniteDimensional ℝ W := Module.Finite.of_basis b
  let b0 := b.map e
  let c0 := MeasureTheory.volume.real (ZSpan.fundamentalDomain b0)
  have hc0 : 0 ≤ c0 := MeasureTheory.measureReal_nonneg
  refine ⟨(finrank ℝ V : ℝ) ^ ((finrank ℝ V : ℝ) / 2) * (Δ * c0) / ε ^ (finrank ℝ V - 1),
    fun T h0 hΔ hmin => ?_⟩
  let T' : W ≃ₗ[ℝ] W := LinearMap.equivOfDetNeZero T h0
  have hT' : ∀ x, T' x = T x := fun x => rfl
  let f := T'.trans e
  let b1 := b.map f
  let L := span ℤ (Set.range b1)
  have hL : ∀ y, y ∈ L ↔ f.symm y ∈ span ℤ (Set.range b) := by
    intro y
    rw [Basis.mem_span_iff_repr_mem, Basis.mem_span_iff_repr_mem]
    simp [b1]
  have hcov : ZLattice.covolume L = |LinearMap.det T| * c0 := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ MeasureTheory.volume
      (ZSpan.isAddFundamentalDomain b1 MeasureTheory.volume),
      ZSpan.measureReal_fundamentalDomain b1 MeasureTheory.volume b0]
    congr 2
    have : (b1 : ι → V) = e ∘ (T ∘ b) := by
      ext i; simp [b1, f, hT']
    rw [this, Basis.det_map]
    have h3 : (e.symm : V → W) ∘ e ∘ T ∘ b = T ∘ b := by ext i; simp
    rw [h3, Basis.det_comp, Basis.det_self, mul_one]
  obtain ⟨v, hv, hN⟩ := exists_basis_norm_eq_succMin L
  refine ⟨v.map f.symm, fun i => ⟨(hL _).1 (hv i), ?_⟩⟩
  have h1 : e (T (v.map f.symm i)) = v i := f.apply_symm_apply (v i)
  rw [h1, hN, le_div_iff₀ (by positivity)]
  have hne : L ≠ ⊥ := fun h => v.ne_zero i (by simpa [h] using hv i)
  have hm : ε ≤ minNorm L := le_minNorm hne fun y hy hy0 => by
    have := hmin _ ((hL y).1 hy) (by simpa using hy0)
    rwa [show e (T (f.symm y)) = y from f.apply_symm_apply y] at this
  have h2 := succMin_mul_minNorm_pow_le L (k := i + 1) (by omega) i.2
  refine le_trans ?_ (h2.trans ?_)
  · have := succMin_nonneg L (i + 1)
    gcongr
  · rw [hcov]; gcongr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}

theorem prod_type {M : Type} [CommMonoid M] (h : IsType Ψ) (f : (E →+* ℂ) → M) :
    ∏ σ, f σ = ∏ τ : Ψ, (f τ.1 * f (ComplexEmbedding.conjugate τ.1)) := by
  classical
  rw [Finset.prod_mul_distrib, Finset.prod_coe_sort Ψ f,
    Finset.prod_coe_sort Ψ fun τ => f (ComplexEmbedding.conjugate τ),
    ← Finset.prod_mul_prod_compl Ψ f]
  congr 1
  symm
  refine Finset.prod_bij' (fun τ _ => ComplexEmbedding.conjugate τ)
    (fun τ _ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simpa using (h a).1 ha
  · intro a ha
    have := h a
    simp only [Finset.mem_compl] at ha
    tauto
  · intro a _; exact star_star a
  · intro a _; exact star_star a
  · intro a _; rfl

theorem one_le_prod (h : IsType Ψ) {a : E} (ha : IsIntegral ℤ a) (h0 : a ≠ 0) :
    1 ≤ ∏ τ : Ψ, ‖τ.1 a‖ := by
  have h1 : (1 : ℝ) ≤ ∏ σ : E →+* ℂ, ‖σ a‖ := by
    have h2 := Algebra.norm_eq_prod_embeddings ℚ ℂ a
    have h3 : ∏ σ : E →+* ℂ, σ a = ∏ σ : E →ₐ[ℚ] ℂ, σ a :=
      Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) _ _ fun _ => rfl
    rw [← norm_prod, h3, ← h2]
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm ℚ ha)
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact h0 (by simpa using hz.symm)
    rw [← hz]
    simp only [eq_intCast, map_intCast, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hz0
  rw [prod_type h] at h1
  simp only [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj, Finset.prod_mul_distrib] at h1
  have : 0 ≤ ∏ τ : Ψ, ‖τ.1 a‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  nlinarith

theorem card_type (h : IsType Ψ) : finrank ℚ E = Ψ.card * 2 := by
  have := prod_type (M := Multiplicative ℕ) h fun _ => Multiplicative.ofAdd 1
  rw [← Embeddings.card E ℂ]
  have h2 := congrArg Multiplicative.toAdd this
  simpa using h2

theorem basis_one (h : IsType Ψ) : ∃ b : Basis (Free.ChooseBasisIndex ℤ (𝓞 E)) ℝ (Ψ → ℂ),
    ∀ x, x ∈ span ℤ (Set.range b) ↔ ∃ a : E, IsIntegral ℤ a ∧ x = fun τ => τ.1 a := by
  classical
  let u : Free.ChooseBasisIndex ℤ (𝓞 E) → Ψ → ℂ := fun j τ => τ.1 (integralBasis E j)
  have hli : LinearIndependent ℝ u := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h1 := Fintype.linearIndependent_iff.1 (canonicalEmbedding.latticeBasis E).linearIndependent
      (fun j => (c j : ℂ)) ?_ j
    · exact_mod_cast h1
    have key : ∀ τ ∈ Ψ, ∑ j, (c j : ℂ) * τ (integralBasis E j) = 0 := fun τ hτ => by
      simpa [u] using congrFun hc ⟨τ, hτ⟩
    ext σ
    simp only [canonicalEmbedding.latticeBasis_apply, Finset.sum_apply, Pi.smul_apply,
      canonicalEmbedding.apply_at, smul_eq_mul, Pi.zero_apply]
    by_cases hσ : σ ∈ Ψ
    · exact key σ hσ
    · have h2 : ComplexEmbedding.conjugate σ ∈ Ψ := by
        have := h σ; tauto
      have := congrArg conj (key _ h2)
      simpa using this
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 E)) = finrank ℝ (Ψ → ℂ) := by
    rw [← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, card_type h,
      Module.finrank_pi_fintype]
    simp
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' u hli hcard, fun x => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank']
  let φ : E →ₗ[ℤ] (Ψ → ℂ) := (AddMonoidHom.pi fun τ : Ψ => τ.1.toAddMonoidHom).toIntLinearMap
  have : Set.range u = φ '' Set.range (integralBasis E) := by
    rw [← Set.range_comp]; rfl
  rw [this, span_image, Submodule.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨z, rfl⟩ := (mem_span_integralBasis E).1 ha
    exact ⟨_, z.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, (mem_span_integralBasis E).2 ⟨⟨a, ha⟩, rfl⟩, rfl⟩

theorem basis_many (h : IsType Ψ) (m : ℕ) :
    ∃ b : Basis (Σ _ : Fin m, Free.ChooseBasisIndex ℤ (𝓞 E)) ℝ (Ψ → Fin m → ℂ),
    ∀ x, x ∈ span ℤ (Set.range b) ↔
      ∃ v : Fin m → E, (∀ a, IsIntegral ℤ (v a)) ∧ x = fun τ a => τ.1 (v a) := by
  obtain ⟨b, hb⟩ := basis_one h
  let e : (Fin m → Ψ → ℂ) ≃ₗ[ℝ] (Ψ → Fin m → ℂ) :=
    { toFun := fun x τ a => x a τ, invFun := fun x a τ => x τ a, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  refine ⟨(Pi.basis fun _ => b).map e, fun x => ?_⟩
  have : x ∈ span ℤ (Set.range ((Pi.basis fun _ : Fin m => b).map e)) ↔
      ∀ a, (fun τ => x τ a) ∈ span ℤ (Set.range b) := by
    simp only [Basis.mem_span_iff_repr_mem, Sigma.forall]
    rfl
  rw [this]
  simp only [hb]
  constructor
  · intro hx
    choose v hv hx using hx
    exact ⟨v, hv, by ext τ a; exact congrFun (hx a) τ⟩
  · rintro ⟨v, hv, rfl⟩ a
    exact ⟨v a, hv a, rfl⟩

theorem fac {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.PosDef) :
    ∃ B : Matrix (Fin m) (Fin m) ℂ, H = B * Bᴴ ∧ (∀ x y : Fin m → ℂ, x ⬝ᵥ H *ᵥ star y =
      inner ℂ (WithLp.toLp 2 (y ᵥ* B)) (WithLp.toLp 2 (x ᵥ* B))) ∧
      ∀ x : Fin m → ℂ, (x ⬝ᵥ H *ᵥ star x).re = ‖WithLp.toLp 2 (x ᵥ* B)‖ ^ 2 := by
  open MatrixOrder in
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hH.posSemidef.nonneg
  have h1 : H = Bᴴ * Bᴴᴴ := by simpa [star_eq_conjTranspose] using hB
  have h2 : ∀ x y : Fin m → ℂ, x ⬝ᵥ H *ᵥ star y =
      inner ℂ (WithLp.toLp 2 (y ᵥ* Bᴴ)) (WithLp.toLp 2 (x ᵥ* Bᴴ)) := by
    intro x y
    rw [EuclideanSpace.inner_toLp_toLp, h1, ← mulVec_mulVec, dotProduct_mulVec, star_vecMul]
  refine ⟨Bᴴ, h1, h2, fun x => ?_⟩
  rw [h2, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rfl

theorem hval_eq {m : ℕ} (H : CM Ψ m m) (τ : Ψ) (v : Fin m → E) :
    hval Ψ H τ v = ((fun a => τ.1 (v a)) ⬝ᵥ H τ *ᵥ star fun a => τ.1 (v a)).re := rfl

theorem short (h : IsType Ψ) (m : ℕ) (Δ ε : ℝ) (hε : 0 < ε) : ∃ (n : ℕ) (C : ℝ),
    ∀ H : CM Ψ m m, (∀ τ, (H τ).PosDef) → ∏ τ, ‖(H τ).det‖ ≤ Δ →
    (∀ v : Fin m → E, v ≠ 0 → (∀ a, IsIntegral ℤ (v a)) → ε ≤ ∑ τ, hval Ψ H τ v) →
    ∃ V : Matrix (Fin n) (Fin m) E, IntM V ∧ (∃ S : Matrix (Fin m) (Fin n) E, S * V = 1) ∧
      ∀ i τ, hval Ψ H τ (V i) ≤ C := by
  classical
  obtain ⟨b, hb⟩ := basis_many h m
  let e : (Ψ → Fin m → ℂ) ≃ₗ[ℝ] PiLp 2 (fun _ : Ψ => EuclideanSpace ℂ (Fin m)) :=
    (LinearEquiv.piCongrRight fun _ => (WithLp.linearEquiv 2 ℝ (Fin m → ℂ)).symm).trans
      (WithLp.linearEquiv 2 ℝ _).symm
  have he : ∀ x, ‖e x‖ ^ 2 = ∑ τ, ‖WithLp.toLp 2 (x τ)‖ ^ 2 := fun x =>
    PiLp.norm_sq_eq_of_L2 _ _
  obtain ⟨C, hC⟩ := mink b e Δ (√ε) (Real.sqrt_pos.2 hε)
  refine ⟨finrank ℝ (PiLp 2 fun _ : Ψ => EuclideanSpace ℂ (Fin m)), C ^ 2,
    fun H hH hΔ hmin => ?_⟩
  choose B hB1 hB2 hB3 using fun τ => fac (hH τ)
  let T : (Ψ → Fin m → ℂ) →ₗ[ℝ] (Ψ → Fin m → ℂ) := LinearMap.pi fun τ =>
    ((Matrix.toLin' (B τ)ᵀ).restrictScalars ℝ).comp (LinearMap.proj τ)
  have hT : ∀ x τ, T x τ = x τ ᵥ* B τ := fun x τ => by simp [T, mulVec_transpose]
  have hdet : LinearMap.det T = ∏ τ, ‖(H τ).det‖ := by
    rw [LinearMap.det_pi]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, LinearMap.det_toLin',
      det_transpose, hB1 τ, det_mul, det_conjTranspose, norm_mul, norm_star, Complex.normSq_eq_norm_sq,
      sq]
  have hq : ∀ v : Fin m → E, ‖e (T fun τ a => τ.1 (v a))‖ ^ 2 = ∑ τ, hval Ψ H τ v := by
    intro v
    rw [he]
    exact Finset.sum_congr rfl fun τ _ => by rw [hT, hval_eq, hB3]
  obtain ⟨v, hv⟩ := hC T
    (by rw [hdet]; exact Finset.prod_ne_zero_iff.2 fun τ _ => norm_ne_zero_iff.2 (hH τ).det_pos.ne')
    (by rwa [hdet, abs_of_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)])
    (by
      intro x hx h0
      obtain ⟨w, hw, rfl⟩ := (hb x).1 hx
      rw [Real.sqrt_le_left (norm_nonneg _), hq]
      exact hmin w (by rintro rfl; exact h0 (by ext; simp)) hw)
  choose w hw hvw using fun i => (hb _).1 (hv i).1
  refine ⟨Matrix.of w, fun i a => hw i a, ?_, fun i τ => ?_⟩
  · have hinj : LinearMap.ker (Matrix.toLin' (Matrix.of w)) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro c hc
      obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
      obtain ⟨τ⟩ : Nonempty Ψ := by
        by_cases hσ : σ ∈ Ψ
        · exact ⟨⟨σ, hσ⟩⟩
        · exact ⟨⟨ComplexEmbedding.conjugate σ, by have := h σ; tauto⟩⟩
      let l : (Ψ → Fin m → ℂ) →ₗ[ℝ] ℂ :=
        { toFun := fun x => ∑ a, x τ a * τ.1 (c a)
          map_add' := fun x y => by simp [add_mul, Finset.sum_add_distrib]
          map_smul' := fun r x => by simp [Finset.mul_sum, mul_assoc] }
      have hl : l = 0 := v.ext fun i => by
        have := congrArg τ.1 (congrFun hc i)
        rw [hvw i]
        simpa [l, mulVec, dotProduct] using this
      ext a
      have := LinearMap.congr_fun hl fun _ => Pi.single a 1
      simpa [l, Pi.single_apply] using this
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
    refine ⟨LinearMap.toMatrix' g, ?_⟩
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  · have h1 := (hv i).2
    rw [hvw i] at h1
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [hq] at h2
    refine le_trans ?_ h2
    exact Finset.single_le_sum (f := fun τ => hval Ψ H τ (w i))
      (fun τ _ => by rw [hval_eq, hB3]; positivity) (Finset.mem_univ τ)

theorem gram_le {m : ℕ} {H G : Matrix (Fin m) (Fin m) ℂ} (hH : H.PosDef) (hG : Gᴴ = G)
    (h0 : G.det ≠ 0) (hm : H * G⁻¹ * H = G) (x y : Fin m → ℂ) {C : ℝ}
    (hx : (x ⬝ᵥ H *ᵥ star x).re ≤ C) (hy : (y ⬝ᵥ H *ᵥ star y).re ≤ C) :
    ‖x ⬝ᵥ G *ᵥ star y‖ ≤ C := by
  obtain ⟨B, -, h2, h3⟩ := fac hH
  have hG' : (G⁻¹)ᴴ = G⁻¹ := by rw [conjTranspose_nonsing_inv, hG]
  have h4' : ∀ y, x ⬝ᵥ G *ᵥ y = (x ᵥ* (H * G⁻¹)) ⬝ᵥ H *ᵥ y := fun y => by
    rw [← dotProduct_mulVec, mulVec_mulVec, hm]
  have h5 : (x ᵥ* (H * G⁻¹)) ⬝ᵥ H *ᵥ star (x ᵥ* (H * G⁻¹)) = x ⬝ᵥ H *ᵥ star x := by
    rw [← h4', star_vecMul, mulVec_mulVec, conjTranspose_mul, hG', hH.1.eq,
      mul_nonsing_inv_cancel_left _ _ h0.isUnit]
  rw [← h5, h3] at hx
  rw [h3] at hy
  rw [h4', h2]
  refine (norm_inner_le_norm _ _).trans ?_
  nlinarith [sq_nonneg (‖WithLp.toLp 2 (y ᵥ* B)‖ - ‖WithLp.toLp 2 ((x ᵥ* (H * G⁻¹)) ᵥ* B)‖)]

theorem comb_le {m n : ℕ} {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.PosDef)
    (x : Fin n → Fin m → ℂ) (t : Fin n → ℂ) {C M : ℝ}
    (hx : ∀ j, (x j ⬝ᵥ H *ᵥ star (x j)).re ≤ C) (ht : ∀ j, ‖t j‖ ≤ M) :
    ((∑ j, t j • x j) ⬝ᵥ H *ᵥ star (∑ j, t j • x j)).re ≤ (n * (M * √C)) ^ 2 := by
  obtain ⟨B, -, -, h3⟩ := fac hH
  rw [h3]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  have : WithLp.toLp 2 ((∑ j, t j • x j) ᵥ* B) = ∑ j, t j • WithLp.toLp 2 (x j ᵥ* B) := by
    simp [sum_vecMul, smul_vecMul]
  rw [this]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (M * √C) fun j _ => ?_).trans
    (by simp))
  rw [norm_smul]
  have h4 := hx j
  rw [h3] at h4
  exact mul_le_mul (ht j) (Real.le_sqrt_of_sq_le h4) (norm_nonneg _) ((norm_nonneg _).trans (ht j))

theorem emb_cc (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) :=
  IsCMField.complexEmbedding_complexConj E τ x

theorem ccT_mul {α β γ : Type} [Fintype β] (A : Matrix α β E) (B : Matrix β γ E) :
    ccT (A * B) = ccT B * ccT A := by
  ext i j
  simp [ccT, cc, Matrix.mul_apply, mul_comm]

theorem ccT_smul {α β : Type} (k : ℤ) (A : Matrix α β E) :
    ccT ((k : E) • A) = (k : E) • ccT A := by
  ext i j
  simp [ccT, cc]

theorem ccT_one {α : Type} [DecidableEq α] : ccT (1 : Matrix α α E) = 1 := by
  ext i j
  simp [ccT, cc, Matrix.one_apply, apply_ite, eq_comm]

omit [NumberField E] [IsCMField E] in
theorem intM_mul {α β γ : Type} [Fintype β] {A : Matrix α β E} {B : Matrix β γ E} (hA : IntM A)
    (hB : IntM B) : IntM (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact IsIntegral.sum _ fun k _ => (hA i k).mul (hB k j)

theorem intM_ccT {α β : Type} {A : Matrix α β E} (hA : IntM A) : IntM (ccT A) := fun i j =>
  (hA j i).map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom

omit [NumberField E] [IsCMField E] in
theorem li_of_mul {k a b : ℕ} {A : Matrix (Fin k) (Fin a) E} {R : Matrix (Fin a) (Fin b) E}
    (h : LinearIndependent E fun i => (A * R) i) : LinearIndependent E fun i => A i :=
  LinearIndependent.of_comp (Matrix.vecMulLinear R) h

theorem det_le (h : IsType Ψ) {m D : ℕ} (hD : 0 < D) {G : Matrix (Fin m) (Fin m) E}
    {H : CM Ψ m m} (h0 : G.det ≠ 0) (hG : Den D G⁻¹) (hH : IsMaj Ψ G H) :
    ∏ τ, ‖(H τ).det‖ ≤ ∏ _τ : Ψ, (D : ℝ) ^ m := by
  have ha : IsIntegral ℤ ((D : E) • G⁻¹).det := IsIntegral.det hG
  have hd : ((D : E) • G⁻¹).det = (D : E) ^ m * (G.det)⁻¹ := by simp
  have hD' : (D : E) ≠ 0 := by exact_mod_cast hD.ne'
  have h1 := one_le_prod h ha (by rw [hd]; exact mul_ne_zero (pow_ne_zero _ hD') (inv_ne_zero h0))
  refine (le_mul_of_one_le_right (Finset.prod_nonneg fun _ _ => norm_nonneg _) h1).trans_eq ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h2 := congrArg (fun A => ‖Matrix.det A‖) (hH τ).2
  have h3 : (G.map τ.1).det = τ.1 G.det := (RingHom.map_det _ _).symm
  have h4 : 0 < ‖τ.1 G.det‖ := by simpa using h0
  simp only [det_mul, det_nonsing_inv, Ring.inverse_eq_inv', h3, norm_mul, norm_inv] at h2
  have h5 : ‖(H τ).det‖ = ‖τ.1 G.det‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) h4.le]
    field_simp at h2
    exact h2
  rw [hd, h5]
  simp only [map_mul, map_pow, map_natCast, map_inv₀, norm_mul, norm_pow, norm_inv,
    Complex.norm_natCast]
  field_simp

def IsoRows' {k n : ℕ} (Γ : Matrix (Fin n) (Fin n) E) (T : Matrix (Fin k) (Fin n) E) : Prop :=
  LinearIndependent E (fun i => (T * Γ) i) ∧ T * Γ * ccT T = 0

theorem exists_int_rows {N m n D : ℕ} (hD : 0 < D) {G : Matrix (Fin m) (Fin m) E} (h0 : G.det ≠ 0)
    {W : Matrix (Fin N) (Fin m) E} (hW : IsoRows G W) {V : Matrix (Fin n) (Fin m) E}
    {S : Matrix (Fin m) (Fin n) E} (hS : S * V = 1) :
    ∃ T : Matrix (Fin N) (Fin n) E, IntM T ∧ IsoRows' (V * ((D : E) • G) * ccT V) T := by
  classical
  obtain ⟨k, hk, hint⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : Fin N × Fin n => (W * S) p.1 p.2)
  have hD' : (D : E) ≠ 0 := by exact_mod_cast hD.ne'
  have hk' : (k : E) ≠ 0 := by exact_mod_cast hk
  have h1 : ((k : E) • (W * S)) * V = (k : E) • W := by
    rw [Matrix.smul_mul, Matrix.mul_assoc, hS, Matrix.mul_one]
  have h2 : ccT V * ccT S = 1 := by rw [← ccT_mul, hS, ccT_one]
  refine ⟨(k : E) • (W * S), fun i j => ?_, ?_, ?_⟩
  · simpa using hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
  · refine li_of_mul (R := ((k : E)⁻¹ * (D : E)⁻¹) • (ccT S * G⁻¹)) ?_
    have : (k : E) • (W * S) * (V * ((D : E) • G) * ccT V) *
        ((k : E)⁻¹ * (D : E)⁻¹) • (ccT S * G⁻¹) = W := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_smul, Matrix.mul_assoc,
        ← Matrix.mul_assoc (ccT V), h2]
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.one_mul,
        mul_nonsing_inv_cancel_right _ _ h0.isUnit]
      rw [show (k : E)⁻¹ * (D : E)⁻¹ * (D * k) = 1 by field_simp, one_smul]
    rw [this]
    exact hW.1
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (ccT V), ← ccT_mul, h1, ccT_smul]
    simp [hW.2]

end GlobalTheory.SW.MinkowskiProductBounds

open GlobalTheory.SW.MinkowskiProductBounds in

theorem GlobalTheory.SW.exists_shortIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (N D : ℕ) (ε : ℝ), 0 < D → 0 < ε →
    ∃ C : ℝ, ShortIso Ψ N D ε C := by
  intro E _ _ _ Ψ h N D ε hD hε
  classical
  obtain ⟨n, C, hC⟩ := short h (2 * N) (∏ _τ : Ψ, (D : ℝ) ^ (2 * N)) ε hε
  let F : Set (Matrix (Fin n) (Fin n) E) :=
    {Γ | ∀ i j, Γ i j ∈ {x : E | IsIntegral ℤ x ∧ ∀ σ : E →+* ℂ, ‖σ x‖ ≤ D * C}}
  have hF : F.Finite :=
    Set.Finite.pi' fun _ => Set.Finite.pi' fun _ => Embeddings.finite_of_norm_le E ℂ _
  have hex : ∀ Γ : Matrix (Fin n) (Fin n) E, ∃ T : Matrix (Fin N) (Fin n) E,
      (∃ T : Matrix (Fin N) (Fin n) E, IntM T ∧ IsoRows' Γ T) → IntM T ∧ IsoRows' Γ T := by
    intro Γ
    by_cases hΓ : ∃ T : Matrix (Fin N) (Fin n) E, IntM T ∧ IsoRows' Γ T
    · exact ⟨hΓ.choose, fun _ => hΓ.choose_spec⟩
    · exact ⟨0, fun h => absurd h hΓ⟩
  choose T hT using hex
  obtain ⟨M, hM⟩ := ((hF.prod (Set.finite_univ (α := Ψ × Fin N × Fin n))).image
    fun p => ‖p.2.1.1 (T p.1 p.2.2.1 p.2.2.2)‖).bddAbove
  refine ⟨(n * (M * √C)) ^ 2, fun G H hG h0 hD1 hD2 ⟨W, hW⟩ hH hmin => ?_⟩
  obtain ⟨V, hV, ⟨S, hS⟩, hVC⟩ := hC H (fun τ => (hH τ).1) (det_le h hD h0 hD2 hH) hmin
  set Γ := V * ((D : E) • G) * ccT V with hΓ
  have hΓF : Γ ∈ F := by
    intro i j
    refine ⟨intM_mul (intM_mul hV hD1) (intM_ccT hV) i j, ?_⟩
    have key : ∀ τ : Ψ, ‖τ.1 (Γ i j)‖ ≤ D * C := by
      intro τ
      have h1 : (G.map τ.1)ᴴ = G.map τ.1 := by
        ext a b
        have := congrArg τ.1 (congrFun (congrFun hG a) b)
        simpa [ccT, emb_cc] using this
      have h2 : (G.map τ.1).det ≠ 0 := by
        rw [show (G.map τ.1).det = τ.1 G.det from (RingHom.map_det _ _).symm]
        simpa using h0
      have h3 := gram_le (hH τ).1 h1 h2 (hH τ).2 _ _ (hVC i τ) (hVC j τ)
      have h4 : τ.1 (Γ i j) = D * ((fun a => τ.1 (V i a)) ⬝ᵥ G.map τ.1 *ᵥ
          star fun a => τ.1 (V j a)) := by
        rw [hΓ, Matrix.mul_assoc]
        simp [Matrix.mul_apply, ccT, emb_cc, dotProduct, mulVec, Finset.mul_sum, mul_assoc,
          mul_left_comm]
      rw [h4, norm_mul, Complex.norm_natCast]
      gcongr
    intro σ
    by_cases hσ : σ ∈ Ψ
    · exact key ⟨σ, hσ⟩
    · simpa using key ⟨ComplexEmbedding.conjugate σ, by have := h σ; tauto⟩
  obtain ⟨hT1, hT2, hT3⟩ := hT Γ (exists_int_rows hD h0 hW hS)
  refine ⟨T Γ * V, intM_mul hT1 hV, ⟨?_, ?_⟩, fun i τ => ?_⟩
  · refine li_of_mul (R := ((D : E) • G) * ccT V) ?_
    rwa [Matrix.mul_assoc, ← Matrix.mul_assoc V]
  · have hD' : (D : E) ≠ 0 := by exact_mod_cast hD.ne'
    refine (smul_eq_zero_iff_right hD').1 ?_
    rw [← hT3, ccT_mul]
    simp only [hΓ, Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
  · have h1 : (fun a => τ.1 ((T Γ * V) i a)) = ∑ j, τ.1 (T Γ i j) • fun a => τ.1 (V j a) := by
      ext a
      simp [Matrix.mul_apply]
    rw [hval_eq, h1]
    exact comb_le (hH τ).1 _ _ (fun j => hVC j τ) fun j =>
      hM ⟨(Γ, τ, i, j), ⟨hΓF, trivial⟩, rfl⟩
