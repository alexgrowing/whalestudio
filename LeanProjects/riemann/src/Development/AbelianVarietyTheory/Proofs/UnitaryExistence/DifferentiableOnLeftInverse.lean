import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RiemannRel

variable {g : ℕ}

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {g : ℕ} in

theorem _root_.GlobalTheory.RiemannRel.hermForm_mulVec (G A B : Matrix (Fin g) (Fin g) ℂ) (v w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (A *ᵥ v) (B *ᵥ w) = v ⬝ᵥ (Aᵀ * G * B.map (starRingEnd ℂ)) *ᵥ star w := by
  have hstar : star (B *ᵥ w) = B.map (starRingEnd ℂ) *ᵥ star w := by
    ext i; simp [mulVec, dotProduct, star_sum]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  rw [hstar, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v Aᵀ,
    Matrix.vecMul_transpose, Matrix.mulVec_mulVec]

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {g : ℕ} in
theorem _root_.GlobalTheory.RiemannRel.hermForm_col (G A B : Matrix (Fin g) (Fin g) ℂ) (j k : Fin g) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (A *ᵥ Pi.single j 1) (B *ᵥ Pi.single k 1) = (Aᵀ * G * B.map (starRingEnd ℂ)) j k := by
  rw [_root_.GlobalTheory.RiemannRel.hermForm_mulVec]; simp [Pi.star_single]

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {g : ℕ} in

theorem _root_.GlobalTheory.RiemannRel.det_ne_zero (G A B : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G z z).re)
    (hM : ∀ j k, ((Aᵀ * G * A.map (starRingEnd ℂ)) j k).im = 0)
    (hN : ∀ j k, ((Aᵀ * G * B.map (starRingEnd ℂ)) j k).im = -(1 : Matrix (Fin g) (Fin g) ℝ) j k) :
    A.det ≠ 0 := by
  intro hA0
  obtain ⟨v, hv0, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hA0
  have hreal : ∀ r s : Fin g → ℝ,
      (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (A *ᵥ fun j => (r j : ℂ)) (A *ᵥ fun j => (s j : ℂ))).im = 0 := by
    intro r s
    rw [_root_.GlobalTheory.RiemannRel.hermForm_mulVec]
    simp [dotProduct, mulVec, Complex.im_sum, Complex.mul_im, hM]
  have hcross : ∀ (r : Fin g → ℝ) (k : Fin g),
      (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (A *ᵥ fun j => (r j : ℂ)) (B *ᵥ Pi.single k 1)).im = -r k := by
    intro r k
    rw [_root_.GlobalTheory.RiemannRel.hermForm_mulVec, Pi.star_single, star_one, Matrix.mulVec_single_one]
    simp [dotProduct, Complex.im_sum, Complex.mul_im, hN, Matrix.one_apply]
  set x : Fin g → ℂ := fun j => ((v j).re : ℂ) with hx
  set y : Fin g → ℂ := fun j => ((v j).im : ℂ) with hy
  have hv : v = x + Complex.I • y := by
    ext j; simp only [x, y, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm]; exact (Complex.re_add_im _).symm
  have hAx : A *ᵥ x = -(Complex.I • A *ᵥ y) := by
    rw [hv, Matrix.mulVec_add, Matrix.mulVec_smul] at hAv
    exact eq_neg_of_add_eq_zero_left hAv
  have hform : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (A *ᵥ x) (A *ᵥ x) = Complex.I * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (A *ᵥ x) (A *ᵥ y) := by
    conv_lhs => arg 3; rw [hAx]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
    simp [star_neg, star_smul, Matrix.mulVec_neg, Matrix.mulVec_smul, dotProduct_smul]
  have hx0 : A *ᵥ x = 0 := by
    by_contra hne
    have h1 := hpos _ hne
    rw [hform, Complex.mul_re, Complex.I_re, Complex.I_im, hreal] at h1
    simp at h1
  have hy0 : A *ᵥ y = 0 := by
    rw [hx0, eq_comm, neg_eq_zero, smul_eq_zero] at hAx
    exact hAx.resolve_left Complex.I_ne_zero
  apply hv0
  ext k
  have h1 := hcross (fun j => (v j).re) k
  have h2 := hcross (fun j => (v j).im) k
  change (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (A *ᵥ x) _).im = _ at h1
  change (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (A *ᵥ y) _).im = _ at h2
  rw [hx0] at h1
  rw [hy0] at h2
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, zero_dotProduct, Complex.zero_im, zero_eq_neg] at h1 h2
  apply Complex.ext
  · simpa using h1
  · simpa using h2

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {g : ℕ} in

theorem _root_.GlobalTheory.RiemannRel.symm_posDef (G A τ : Matrix (Fin g) (Fin g) ℂ) (hG : G.IsHermitian)
    (hA : A.det ≠ 0)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G z z).re)
    (hM : ∀ j k, ((Aᵀ * G * A.map (starRingEnd ℂ)) j k).im = 0)
    (hN : ∀ j k, ((Aᵀ * G * (A * τ).map (starRingEnd ℂ)) j k).im = -(1 : Matrix (Fin g) (Fin g) ℝ) j k)
    (hK : ∀ j k, (((A * τ)ᵀ * G * (A * τ).map (starRingEnd ℂ)) j k).im = 0) :
    τ.IsSymm ∧ (τ.map Complex.im).PosDef := by
  set M := Aᵀ * G * A.map (starRingEnd ℂ) with hMdef
  set S : Matrix (Fin g) (Fin g) ℝ := M.map Complex.re with hSdef
  set X : Matrix (Fin g) (Fin g) ℝ := τ.map Complex.re with hXdef
  set Y : Matrix (Fin g) (Fin g) ℝ := τ.map Complex.im with hYdef
  have hMh : Mᴴ = M := by
    have h1 : (A.map (starRingEnd ℂ))ᴴ = Aᵀ := by ext i j; simp
    have h2 : (Aᵀ)ᴴ = A.map (starRingEnd ℂ) := by ext i j; simp
    rw [hMdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, h1, h2, hG.eq, Matrix.mul_assoc]
  have hSsymm : ∀ j k, S k j = S j k := by
    intro j k
    have := congrFun (congrFun hMh j) k
    rw [Matrix.conjTranspose_apply] at this
    simp only [S, Matrix.map_apply, ← this, Complex.star_def, Complex.conj_re]
  have hSh : S.IsHermitian := by
    ext j k; simp [hSsymm]
  have hN' : Aᵀ * G * (A * τ).map (starRingEnd ℂ) = M * τ.map (starRingEnd ℂ) := by
    rw [Matrix.map_mul, hMdef]; simp only [Matrix.mul_assoc]
  have hSY : S * Y = 1 := by
    ext j k
    have := hN j k
    rw [hN'] at this
    simp only [Matrix.mul_apply, Complex.im_sum, Complex.mul_im, hM, Matrix.map_apply,
      Complex.conj_re, Complex.conj_im, zero_mul, add_zero] at this
    simp only [Matrix.mul_apply, S, Y, Matrix.map_apply]
    linarith [show ∑ x, (M j x).re * -(τ x k).im = -∑ x, (M j x).re * (τ x k).im by
      simp [Finset.sum_neg_distrib]]
  have hSpos : S.PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hSh, fun x hx => ?_⟩
    have hAx : A *ᵥ (fun j => (x j : ℂ)) ≠ 0 := by
      intro h0
      apply hx
      ext j
      have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hA h0) j
      simpa using this
    have h := hpos _ hAx
    rw [_root_.GlobalTheory.RiemannRel.hermForm_mulVec] at h
    simpa [dotProduct, mulVec, Complex.re_sum, Complex.mul_re, hM, S] using h
  have hYinv : Y = S⁻¹ := (Matrix.inv_eq_right_inv hSY).symm
  have hYpos : Y.PosDef := hYinv ▸ hSpos.inv
  have hK' : (A * τ)ᵀ * G * (A * τ).map (starRingEnd ℂ) = τᵀ * M * τ.map (starRingEnd ℂ) := by
    rw [Matrix.transpose_mul, Matrix.map_mul, hMdef]; simp only [Matrix.mul_assoc]
  have hKim : ∀ j k, ((τᵀ * M * τ.map (starRingEnd ℂ)) j k).im = (Yᵀ * S * X - Xᵀ * S * Y) j k := by
    intro j k
    simp only [Matrix.mul_apply, Matrix.sub_apply, Complex.im_sum, Complex.re_sum, Complex.mul_im,
      Complex.mul_re, hM, Matrix.map_apply, Matrix.transpose_apply, Complex.conj_re, Complex.conj_im,
      Finset.sum_mul, ← Finset.sum_sub_distrib, S, X, Y]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  have hYS : Yᵀ * S = 1 := by
    have hSt : Sᵀ = S := by ext j k; exact hSsymm j k
    rw [← hSt, ← Matrix.transpose_mul, hSY, Matrix.transpose_one]
  have hXs : ∀ j k, X j k = X k j := by
    intro j k
    have h := hK j k
    rw [hK', hKim, Matrix.mul_assoc Xᵀ, hSY, hYS, Matrix.one_mul, Matrix.mul_one, Matrix.sub_apply,
      Matrix.transpose_apply] at h
    linarith
  have hYs : ∀ j k, Y j k = Y k j := by
    intro j k
    have := congrFun (congrFun hYpos.1 k) j
    simpa using this
  refine ⟨Matrix.IsSymm.ext fun i j => Complex.ext ?_ ?_, hYpos⟩
  · exact hXs j i
  · exact hYs j i

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {g : ℕ} in
theorem _root_.GlobalTheory.RiemannRel.differentiableOn_det {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {B : Set V} (A : V → Matrix (Fin g) (Fin g) ℂ)
    (hA : ∀ i j, DifferentiableOn ℂ (fun b => A b i j) B) :
    DifferentiableOn ℂ (fun b => (A b).det) B := by
  simp only [Matrix.det_apply]
  refine DifferentiableOn.fun_sum fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  refine (differentiableOn_const _).mul ?_
  have hprod : (fun b => ∏ i, A b (σ i) i) = ∏ i, (fun b => A b (σ i) i) := by
    ext b; simp [Finset.prod_apply]
  rw [hprod]
  exact Finset.prod_induction _ (fun f => DifferentiableOn ℂ f B) (fun f f' hf hf' => hf.mul hf')
    (differentiableOn_const 1) fun i _ => hA (σ i) i

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {g : ℕ} in
theorem _root_.GlobalTheory.RiemannRel.differentiableOn_left_inverse {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] {B : Set V}
    (A h : V → Matrix (Fin g) (Fin g) ℂ) (hA : ∀ i j, DifferentiableOn ℂ (fun b => A b i j) B)
    (hh : ∀ b ∈ B, h b * A b = 1) (i j : Fin g) : DifferentiableOn ℂ (fun b => h b i j) B := by
  have hdet : ∀ b ∈ B, (A b).det ≠ 0 := fun b hb hz => by
    have := congrArg Matrix.det (hh b hb)
    rw [Matrix.det_mul, hz, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have hinv : ∀ b ∈ B, h b i j = ((A b).det)⁻¹ * (A b).adjugate i j := fun b hb => by
    rw [(Matrix.inv_eq_left_inv (hh b hb)).symm, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul,
      Ring.inverse_eq_inv']
  refine DifferentiableOn.congr ?_ hinv
  refine ((_root_.GlobalTheory.RiemannRel.differentiableOn_det A hA).inv hdet).mul ?_
  simp only [Matrix.adjugate_apply]
  refine _root_.GlobalTheory.RiemannRel.differentiableOn_det _ fun k l => ?_
  by_cases hk : k = j
  · subst hk; simp only [Matrix.updateRow_self]; exact differentiableOn_const _
  · simp only [Matrix.updateRow_ne hk]; exact hA k l

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {g : ℕ} in

theorem _root_.GlobalTheory.RiemannRel.of_cols_mulVec (c : Fin g → Fin g → ℂ) (k : Fin g) :
    (Matrix.of fun i j => c j i) *ᵥ Pi.single k 1 = c k := by
  ext i; simp [mulVec, dotProduct, Pi.single_apply]

theorem cols_iff (h τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → Fin g → ℂ) :
    (∀ k, h *ᵥ a k = Pi.single k 1 ∧ h *ᵥ b k = τ *ᵥ Pi.single k 1) ↔
      h * (Matrix.of fun i j => a j i) = 1 ∧ τ = h * (Matrix.of fun i j => b j i) := by
  constructor
  · intro H
    constructor
    · ext i j
      have := congrFun (H j).1 i
      simp only [mulVec, dotProduct] at this
      simp [mul_apply, this, one_apply, Pi.single_apply]
    · ext i j
      have := congrFun (H j).2 i
      rw [mulVec_single_one] at this
      simp only [mulVec, dotProduct] at this
      simp [mul_apply, this]
  · rintro ⟨h1, rfl⟩ k
    constructor
    · rw [← of_cols_mulVec a k, mulVec_mulVec, h1, one_mulVec]
    · rw [← mulVec_mulVec, of_cols_mulVec]

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {g : ℕ} in

theorem _root_.GlobalTheory.RiemannRel.riemann_relations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La), (∀ a b, D.EF (bas a) (bas b) = -_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd a b) → (∀ P, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P → ∃ h τ : Matrix (Fin g) (Fin g) ℂ, (∀ k, h *ᵥ P (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h *ᵥ P (bas (Pi.single (Sum.inr k) 1)) = τ *ᵥ Pi.single k 1) ∧ IsUnit h.det ∧ τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ ∀ h' τ' : Matrix (Fin g) (Fin g) ℂ, (∀ k, h' *ᵥ P (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h' *ᵥ P (bas (Pi.single (Sum.inr k) 1)) = τ' *ᵥ Pi.single k 1) → h' = h ∧ τ' = τ) ∧ ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D.La →+ (Fin g → ℂ))) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolPeriods D ty B P → (∀ b ∈ B, (∀ k, h b *ᵥ P b (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h b *ᵥ P b (bas (Pi.single (Sum.inr k) 1)) = τ b *ᵥ Pi.single k 1)) → ∀ i j, DifferentiableOn ℂ (fun b => h b i j) B ∧ DifferentiableOn ℂ (fun b => τ b i j) B := by
  intro E _ _ _ H D g ty bas hEF
  have hnorm : ∀ (Q : D.La →+ (Fin g → ℂ)) (h τ : Matrix (Fin g) (Fin g) ℂ),
      (∀ k, h *ᵥ Q (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧
        h *ᵥ Q (bas (Pi.single (Sum.inr k) 1)) = τ *ᵥ Pi.single k 1) →
      h * Matrix.of (fun i j => Q (bas (Pi.single (Sum.inl j) 1)) i) = 1 ∧
        τ = h * Matrix.of (fun i j => Q (bas (Pi.single (Sum.inr j) 1)) i) := by
    intro Q h τ hQ
    refine ⟨Matrix.ext_of_mulVec_single fun k => ?_, Matrix.ext_of_mulVec_single fun k => ?_⟩
    · rw [← Matrix.mulVec_mulVec,
        _root_.GlobalTheory.RiemannRel.of_cols_mulVec (fun j => Q (bas (Pi.single (Sum.inl j) 1))), (hQ k).1,
        Matrix.one_mulVec]
    · rw [← Matrix.mulVec_mulVec,
        _root_.GlobalTheory.RiemannRel.of_cols_mulVec (fun j => Q (bas (Pi.single (Sum.inr j) 1))), (hQ k).2]
  refine ⟨fun P hP => ?_, fun m B P h τ hP hh i j => ?_⟩
  · obtain ⟨-, -, -, -, G, hG, hpos, hIm⟩ := hP
    set A := Matrix.of (fun i j => P (bas (Pi.single (Sum.inl j) 1)) i) with hAdef
    set C := Matrix.of (fun i j => P (bas (Pi.single (Sum.inr j) 1)) i) with hCdef
    have hAcol : ∀ k, A *ᵥ Pi.single k 1 = P (bas (Pi.single (Sum.inl k) 1)) :=
      fun k => _root_.GlobalTheory.RiemannRel.of_cols_mulVec (fun j => P (bas (Pi.single (Sum.inl j) 1))) k
    have hCcol : ∀ k, C *ᵥ Pi.single k 1 = P (bas (Pi.single (Sum.inr k) 1)) :=
      fun k => _root_.GlobalTheory.RiemannRel.of_cols_mulVec (fun j => P (bas (Pi.single (Sum.inr j) 1))) k
    have hM : ∀ j k, ((Aᵀ * G * A.map (starRingEnd ℂ)) j k).im = 0 := by
      intro j k
      rw [← _root_.GlobalTheory.RiemannRel.hermForm_col, hAcol, hAcol, hIm, hEF]
      simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd, Pi.single_apply]
    have hN : ∀ j k,
        ((Aᵀ * G * C.map (starRingEnd ℂ)) j k).im = -(1 : Matrix (Fin g) (Fin g) ℝ) j k := by
      intro j k
      rw [← _root_.GlobalTheory.RiemannRel.hermForm_col, hAcol, hCcol, hIm, hEF]
      simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd, Pi.single_apply, Matrix.one_apply, @eq_comm _ k j]
    have hK : ∀ j k, ((Cᵀ * G * C.map (starRingEnd ℂ)) j k).im = 0 := by
      intro j k
      rw [← _root_.GlobalTheory.RiemannRel.hermForm_col, hCcol, hCcol, hIm, hEF]
      simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd, Pi.single_apply]
    have hdet : A.det ≠ 0 := _root_.GlobalTheory.RiemannRel.det_ne_zero G A C hpos hM hN
    have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
    have hAC : A * (A⁻¹ * C) = C := Matrix.mul_nonsing_inv_cancel_left A C hu
    have hsp := _root_.GlobalTheory.RiemannRel.symm_posDef G A (A⁻¹ * C) hG hdet hpos hM
      (by rw [hAC]; exact hN) (by rw [hAC]; exact hK)
    refine ⟨A⁻¹, A⁻¹ * C, fun k => ⟨?_, ?_⟩, Matrix.isUnit_nonsing_inv_det A hu, hsp.1, hsp.2, ?_⟩
    · rw [← hAcol, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hu, Matrix.one_mulVec]
    · rw [← hCcol, Matrix.mulVec_mulVec]
    · intro h' τ' hh'
      obtain ⟨h1, h2⟩ := hnorm P h' τ' hh'
      have hinv : h' = A⁻¹ := (Matrix.inv_eq_left_inv h1).symm
      exact ⟨hinv, by rw [h2, hinv]⟩
  · have hent : ∀ (s : Fin g ⊕ Fin g) (i : Fin g),
        DifferentiableOn ℂ (fun b => P b (bas (Pi.single s 1)) i) B :=
      fun s i => differentiableOn_pi.mp (hP.2 _) i
    have hdh : ∀ i j, DifferentiableOn ℂ (fun b => h b i j) B :=
      _root_.GlobalTheory.RiemannRel.differentiableOn_left_inverse
        (fun b => Matrix.of fun i j => P b (bas (Pi.single (Sum.inl j) 1)) i) h
        (fun i j => hent _ i) (fun b hb => (hnorm (P b) (h b) (τ b) (hh b hb)).1)
    refine ⟨hdh i j, DifferentiableOn.congr
      (f := fun b => ∑ l, h b i l * P b (bas (Pi.single (Sum.inr j) 1)) l)
      (DifferentiableOn.fun_sum fun l _ => (hdh i l).mul (hent _ l)) fun b hb => ?_⟩
    rw [(hnorm (P b) (h b) (τ b) (hh b hb)).2]
    simp [Matrix.mul_apply]

end GlobalTheory.RiemannRel
