import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt

open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Published

def LandherrSt : Prop := (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G G' : Matrix (Fin r) (Fin r) E), (∀ a b, FD.cc (G a b) = G b a) → (∀ a b, FD.cc (G' a b) = G' b a) → G.det ≠ 0 → G'.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ p0 : ℕ, (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ G' Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ))) → (∃ z : E, G'.det = z * FD.cc z * G.det) → ∃ γ : GL (Fin r) E, ∀ x y, FD.herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = FD.herm G' x y)

namespace LandherrSt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in

theorem _root_.GlobalTheory.Published.LandherrSt.herm_eq (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y = x ⬝ᵥ (G *ᵥ fun b => _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (y b)) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm
  simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in

theorem _root_.GlobalTheory.Published.LandherrSt.herm_mulVec (G P : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (P *ᵥ x) (P *ᵥ y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Pᵀ * G * P.map _root_.ReciprocityTheory.ChartRestriction.G.FD.cc) x y := by
  rw [_root_.GlobalTheory.Published.LandherrSt.herm_eq, _root_.GlobalTheory.Published.LandherrSt.herm_eq]
  have h : (fun b => _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ((P *ᵥ y) b)) = P.map _root_.ReciprocityTheory.ChartRestriction.G.FD.cc *ᵥ fun b => _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (y b) := by
    funext b
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
    simp [mulVec, dotProduct, map_sum, map_mul]
  rw [h, mulVec_mulVec, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, Matrix.mul_assoc]

end LandherrSt

open NumberField Matrix in
open scoped nonZeroDivisors in
private lemma cc_inv' {E : Type} [Field E] [NumberField E] [IsCMField E] (z : E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.cc z⁻¹ = (_root_.ReciprocityTheory.ChartRestriction.G.FD.cc z)⁻¹ := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
  exact map_inv₀ _ _

open NumberField Matrix in
open scoped nonZeroDivisors in

theorem _root_.GlobalTheory.Published.landherrSt_of_landherr (H : _root_.GlobalTheory.Published.Landherr) :
    _root_.GlobalTheory.Published.LandherrSt := by
  intro E _ _ _ r G G' hG hG' hd hd' hsig hdet
  obtain ⟨z, hz⟩ := hdet
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_mul] at hz
    exact hd' hz
  obtain ⟨P, hP, hPG⟩ :=
    _root_.GlobalTheory.Published.Landherr.of_signature H hG hG'
      hd hd' Set.univ (fun _ => Or.inl trivial) (fun τ _ => hsig τ) ⟨z⁻¹, by
        rw [hz, cc_inv']
        field_simp [_root_.GlobalTheory.Published.cc_ne_zero hz0]⟩
  refine ⟨nonsingInvUnit P (isUnit_iff_ne_zero.2 hP), fun x y => ?_⟩
  rw [show ((nonsingInvUnit P (isUnit_iff_ne_zero.2 hP) : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = P
    from rfl, _root_.GlobalTheory.Published.LandherrSt.herm_mulVec, ← hPG]

namespace LandherrSt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open NumberField Matrix in
open scoped nonZeroDivisors in
private lemma eq_zero_iff_lt_card_filter_eq_zero_of_monotone {r : ℕ} (g : Fin r → ℕ) (hg : Monotone g) (a : Fin r) :
    g a = 0 ↔ (a : ℕ) < (Finset.univ.filter fun b => g b = 0).card := by
  constructor
  · intro ha
    have hsub : Finset.Iic a ⊆ Finset.univ.filter fun b => g b = 0 := by
      intro b hb
      simp only [Finset.mem_Iic] at hb
      simpa using Nat.le_zero.1 (ha ▸ hg hb)
    have := Finset.card_le_card hsub
    simp only [Fin.card_Iic] at this
    omega
  · intro ha
    by_contra hne
    have hsub : (Finset.univ.filter fun b => g b = 0) ⊆ Finset.Iio a := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      simp only [Finset.mem_Iio]
      by_contra hab
      exact hne (Nat.le_zero.1 (hb ▸ hg (not_lt.1 hab)))
    have := Finset.card_le_card hsub
    simp only [Fin.card_Iio] at this
    omega

open NumberField Matrix in
open scoped nonZeroDivisors in
private lemma inv_sqrt_abs_mul_self_mul_inv_sqrt_abs_eq_sign (x : ℝ) (hx : x ≠ 0) :
    (Real.sqrt |x|)⁻¹ * x * (Real.sqrt |x|)⁻¹ = if 0 < x then 1 else -1 := by
  have hpos : 0 < |x| := abs_pos.2 hx
  have hs : Real.sqrt |x| * Real.sqrt |x| = |x| := Real.mul_self_sqrt hpos.le
  have hs0 : Real.sqrt |x| ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  rw [mul_comm, ← mul_assoc, ← mul_inv, hs]
  split_ifs with h
  · rw [abs_of_pos h]; field_simp
  · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) hx)]; field_simp

open NumberField Matrix in
open scoped nonZeroDivisors in
private lemma exists_conjTranspose_mul_mul_eq_sgn_diagonal {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ)
    (hA : A.IsHermitian) (hd : A.det ≠ 0) :
    ∃ (p : ℕ) (M : Matrix (Fin r) (Fin r) ℂ),
      Mᴴ * A * M = diagonal fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn p (a : ℕ) : ℝ) : ℂ) := by
  set U : Matrix (Fin r) (Fin r) ℂ := (hA.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℂ) with hU
  set ev := hA.eigenvalues with hev
  have hspec : Uᴴ * A * U = diagonal (Complex.ofReal ∘ ev) := by
    have := hA.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, ← star_eq_conjTranspose] using this
  have hne : ∀ i, ev i ≠ 0 := by
    intro i h
    apply hd
    rw [hA.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [← hev, h])
  set g : Fin r → ℕ := fun i => if 0 < ev i then 0 else 1 with hg
  set σ := Tuple.sort g
  have hmono : Monotone (g ∘ σ) := Tuple.monotone_sort g
  refine ⟨(Finset.univ.filter fun b => (g ∘ σ) b = 0).card,
    (U * diagonal fun i => (((Real.sqrt |ev i|)⁻¹ : ℝ) : ℂ)).submatrix id σ, ?_⟩
  rw [conjTranspose_submatrix, ← submatrix_id_id A, ← Equiv.coe_refl,
    submatrix_mul_equiv, submatrix_mul_equiv, conjTranspose_mul, diagonal_conjTranspose]
  rw [show ∀ X Y Z : Matrix (Fin r) (Fin r) ℂ, X * Uᴴ * Y * (U * Z) = X * (Uᴴ * Y * U) * Z by
    intro X Y Z; simp only [Matrix.mul_assoc], hspec, diagonal_mul_diagonal, diagonal_mul_diagonal,
    submatrix_diagonal_equiv]
  congr 1
  ext a
  have key := eq_zero_iff_lt_card_filter_eq_zero_of_monotone _ hmono a
  have hsq := inv_sqrt_abs_mul_self_mul_inv_sqrt_abs_eq_sign (ev (σ a)) (hne _)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
  simp only [Function.comp_apply, hg] at key ⊢
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hsq]
  by_cases h : 0 < ev (σ a)
  · simp only [h, if_true, true_iff] at key ⊢
    rw [if_pos key]
  · simp only [h, if_false, one_ne_zero, false_iff] at key ⊢
    rw [if_neg key]

open NumberField Matrix in
open scoped nonZeroDivisors in
private lemma sgn_ne_zero_published_landherr (p a : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn p a ≠ 0 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
  split_ifs <;> norm_num

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in

theorem _root_.GlobalTheory.Published.LandherrSt.exists_gram_eq_sgn {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a) (hd : G.det ≠ 0) (τ : E →+* ℂ) :
    ∃ (p : ℕ) (Q : Matrix (Fin r) (Fin r) ℂ), Q.det ≠ 0 ∧
      _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn p (a : ℕ) : ℝ) : ℂ) := by
  have hA : (G.map τ).IsHermitian := by
    ext i j
    simp [conjTranspose_apply, ← _root_.GlobalTheory.Published.embedding_cc, hG]
  have hAd : (G.map τ).det ≠ 0 := by
    have h := RingHom.map_det τ G
    rw [RingHom.mapMatrix_apply] at h
    rw [← h]
    exact (map_ne_zero τ).2 hd
  obtain ⟨p, M, hM⟩ := exists_conjTranspose_mul_mul_eq_sgn_diagonal _ hA hAd
  have hg : _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G (M.map (starRingEnd ℂ)) =
      diagonal fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn p (a : ℕ) : ℝ) : ℂ) := by
    rw [_root_.GlobalTheory.Published.gram_eq, show (M.map (starRingEnd ℂ))ᵀ = Mᴴ from rfl]
    convert hM using 2
    ext i j
    simp
  refine ⟨p, M.map (starRingEnd ℂ), ?_, hg⟩
  intro h0
  have h := congrArg det hg
  rw [_root_.GlobalTheory.Published.gram_eq, det_mul, det_mul, det_transpose, h0, zero_mul, zero_mul,
    det_diagonal] at h
  refine absurd h.symm (Finset.prod_ne_zero_iff.2 ?_)
  intro a _
  exact Complex.ofReal_ne_zero.2 (sgn_ne_zero_published_landherr p (a : ℕ))

end LandherrSt

open NumberField Matrix in
open scoped nonZeroDivisors in
private lemma one_map_cc {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} :
    (1 : Matrix (Fin r) (Fin r) E).map _root_.ReciprocityTheory.ChartRestriction.G.FD.cc = 1 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
  exact Matrix.map_one _ (map_zero _) (map_one _)

open NumberField Matrix in
open scoped nonZeroDivisors in

theorem _root_.GlobalTheory.Published.landherr_of_landherrSt (H : _root_.GlobalTheory.Published.LandherrSt) :
    _root_.GlobalTheory.Published.Landherr := by
  intro E _ _ _ r G G' hG hG' hd hd' hcong hdet
  obtain ⟨x, hx⟩ := hdet
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hx
    exact div_ne_zero hd hd' hx
  have hsig : ∀ τ : E →+* ℂ, ∃ p0 : ℕ, (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧
      (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G' Q = Matrix.diagonal fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) := by
    intro τ
    obtain ⟨p, Q, hQ, hgram⟩ :=
      _root_.GlobalTheory.Published.LandherrSt.exists_gram_eq_sgn hG hd τ
    obtain ⟨R, hR, hR'⟩ := hcong τ
    have hRu : IsUnit R.det := isUnit_iff_ne_zero.2 hR
    refine ⟨p, ⟨Q, hQ, hgram⟩, R⁻¹ * Q, ?_, ?_⟩
    · rw [det_mul, det_nonsing_inv, Ring.inverse_eq_inv']
      exact mul_ne_zero (inv_ne_zero hR) hQ
    · have h1 : (R⁻¹)ᵀ * Rᵀ = 1 := by
        rw [← transpose_mul, mul_nonsing_inv _ hRu, transpose_one]
      have h2 : R.map (starRingEnd ℂ) * (R⁻¹).map (starRingEnd ℂ) = 1 := by
        rw [← Matrix.map_mul, mul_nonsing_inv _ hRu, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [_root_.GlobalTheory.Published.gram_eq] at hgram ⊢
      rw [hR', transpose_mul, Matrix.map_mul, ← hgram]
      calc Qᵀ * (R⁻¹)ᵀ * (Rᵀ * G.map τ * R.map (starRingEnd ℂ)) *
            ((R⁻¹).map (starRingEnd ℂ) * Q.map (starRingEnd ℂ))
          = Qᵀ * ((R⁻¹)ᵀ * Rᵀ) * G.map τ * (R.map (starRingEnd ℂ) * (R⁻¹).map (starRingEnd ℂ)) *
            Q.map (starRingEnd ℂ) := by simp only [Matrix.mul_assoc]
        _ = Qᵀ * G.map τ * Q.map (starRingEnd ℂ) := by rw [h1, h2, Matrix.mul_one, Matrix.mul_one]
  have hdet' : G'.det = x⁻¹ * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc x⁻¹ * G.det := by
    rw [div_eq_iff hd'] at hx
    rw [cc_inv', hx]
    field_simp [hx0, _root_.GlobalTheory.Published.cc_ne_zero hx0]
  obtain ⟨γ, hγ⟩ := H E r G G' hG hG' hd hd' hsig ⟨x⁻¹, hdet'⟩
  · refine ⟨γ, ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero, ?_⟩
    ext a b
    have h := hγ (fun k => (1 : Matrix (Fin r) (Fin r) E) k a)
      (fun k => (1 : Matrix (Fin r) (Fin r) E) k b)
    rw [_root_.GlobalTheory.Published.LandherrSt.herm_mulVec,
      _root_.GlobalTheory.Published.herm_col, _root_.GlobalTheory.Published.herm_col,
      one_map_cc] at h
    simpa using h.symm

end GlobalTheory.Published
