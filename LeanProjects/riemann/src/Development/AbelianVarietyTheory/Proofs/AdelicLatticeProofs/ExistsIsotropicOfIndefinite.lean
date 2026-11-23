import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsZeroCoordNeZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension

open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.UTrans

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.UTrans.herm_diagonal_self {r : ℕ} (g u : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal g) u u = ∑ i, u i * g i * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (u i) := by
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.herm, diagonal_apply, mul_ite, ite_mul]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.UTrans.exists_isotropic_diagonal {n : ℕ} (hn : 3 ≤ n) {g : Fin n → E}
    (hg : ∀ i, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (g i) = g i) (hg0 : ∀ i, g i ≠ 0)
    (hs : ∀ τ : E →+* ℂ, (∃ i, 0 < (τ (g i)).re) ∧ ∃ j, (τ (g j)).re < 0) :
    ∃ z : Fin n → E, z ≠ 0 ∧ _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal g) z z = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hiso : _root_.GlobalTheory.LocalQuad.HermClass.Isotropy := fun F _ _ ι _ a h5 ha hsgn =>
    _root_.GlobalTheory.LocalQuad.isotropic_of_indefinite _root_.GlobalTheory.QNorm.hasseNormSt F a h5 ha hsgn
  have hsign : ∀ τ : E →+* ℂ, ∃ k : Fin m, 0 < (τ (g k.succ)).re ↔ 0 < (τ (-g 0)).re := by
    intro τ
    obtain ⟨⟨i, hi⟩, j, hj⟩ := hs τ
    have h0 : (τ (g 0)).re ≠ 0 := _root_.GlobalTheory.LocalQuad.HermClass.re_ne_zero τ (hg 0) (hg0 0)
    rw [map_neg, Complex.neg_re]
    by_cases hpos : 0 < (τ (g 0)).re
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
      · exact absurd hj (not_lt.2 hpos.le)
      · exact ⟨k, iff_of_false (not_lt.2 hj.le) (by linarith)⟩
    · have hneg : (τ (g 0)).re < 0 := lt_of_le_of_ne (not_lt.1 hpos) h0
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
      · exact absurd hi hpos
      · exact ⟨k, iff_of_true hi (by linarith)⟩
  have hc : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (-g 0) = -g 0 := by
    show IsCMField.complexConj E (-g 0) = -g 0
    rw [map_neg]
    exact congrArg Neg.neg (hg 0)
  obtain ⟨w, hw⟩ := _root_.GlobalTheory.LocalQuad.HermClass.exists_represent hiso (r := m) (by omega)
    (g := fun k => g k.succ) (fun k => hg _) (fun k => hg0 _) hc (neg_ne_zero.2 (hg0 0)) hsign
  refine ⟨Fin.cons 1 w, fun h => one_ne_zero (α := E) (by simpa using congr_fun h 0), ?_⟩
  rw [_root_.GlobalTheory.UTrans.herm_diagonal_self] at hw ⊢
  rw [Fin.sum_univ_succ]
  have h1 : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (1 : E) = 1 := map_one (IsCMField.complexConj E)
  simp only [Fin.cons_zero, Fin.cons_succ, one_mul, h1, mul_one]
  rw [hw]
  ring

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma herm_eq_dotProduct_mulVec_cc {r : ℕ} (H : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm H x y = x ⬝ᵥ (H *ᵥ fun b => _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (y b)) := by
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.herm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma herm_mulVec_mulVec' {r : ℕ} (G P : Matrix (Fin r) (Fin r) E) (u v : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (P *ᵥ u) (P *ᵥ v) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Pᵀ * G * P.map _root_.ReciprocityTheory.ChartRestriction.G.FD.cc) u v := by
  have hc : (fun b => _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ((P *ᵥ v) b)) = P.map _root_.ReciprocityTheory.ChartRestriction.G.FD.cc *ᵥ fun b => _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (v b) := by
    ext b
    simp [mulVec, dotProduct, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc, map_sum, map_mul]
  rw [herm_eq_dotProduct_mulVec_cc, herm_eq_dotProduct_mulVec_cc, hc, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec u, vecMul_transpose]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma re_mul_cc_eq_normSq_mul_re (τ : E →+* ℂ) (y d : E) :
    (τ (y * d * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc y)).re = Complex.normSq (τ y) * (τ d).re := by
  rw [map_mul, map_mul, _root_.GlobalTheory.Published.embedding_cc, mul_right_comm, Complex.mul_conj,
    Complex.re_ofReal_mul]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma exists_re_pos_of_herm_diagonal_re_pos {r : ℕ} (τ : E →+* ℂ) (d y : Fin r → E)
    (hy : 0 < (τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal d) y y)).re) : ∃ i, 0 < (τ (d i)).re := by
  by_contra h
  push_neg at h
  rw [_root_.GlobalTheory.UTrans.herm_diagonal_self, map_sum, Complex.re_sum] at hy
  refine absurd hy (not_lt.2 (Finset.sum_nonpos fun i _ => ?_))
  rw [re_mul_cc_eq_normSq_mul_re]
  exact mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) (h i)

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma exists_re_neg_of_herm_diagonal_re_neg {r : ℕ} (τ : E →+* ℂ) (d y : Fin r → E)
    (hy : (τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal d) y y)).re < 0) : ∃ i, (τ (d i)).re < 0 := by
  by_contra h
  push_neg at h
  rw [_root_.GlobalTheory.UTrans.herm_diagonal_self, map_sum, Complex.re_sum] at hy
  refine absurd hy (not_lt.2 (Finset.sum_nonneg fun i _ => ?_))
  rw [re_mul_cc_eq_normSq_mul_re]
  exact mul_nonneg (Complex.normSq_nonneg _) (h i)

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.UTrans.exists_isotropic_of_indefinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), (∀ a, σ a = IsCMField.complexConj E a) → _root_.GlobalTheory.UTrans.IsHerm σ G → 3 ≤ n → (∀ τ : E →+* ℂ, (∃ x, 0 < (τ (_root_.GlobalTheory.UTrans.hf σ G x x)).re) ∧ ∃ y, (τ (_root_.GlobalTheory.UTrans.hf σ G y y)).re < 0) → ∃ z : Fin n → E, z ≠ 0 ∧ _root_.GlobalTheory.UTrans.hf σ G z z = 0 := by
  intro E _ _ _ n σ G hσ hG hn hs
  have hf : ∀ x y, _root_.GlobalTheory.UTrans.hf σ G x y = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y := by
    intro x y
    simp only [_root_.GlobalTheory.UTrans.hf, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm, hσ]
    rfl
  have hGc : ∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a := fun a b => by
    rw [← hG.herm a b, hσ]
    rfl
  obtain ⟨P, d, hP, hPd, hd, -⟩ := _root_.GlobalTheory.HermDiag.exists_congr_diagonal_herm hGc
  have hPinv : ∀ x, P *ᵥ (P⁻¹ *ᵥ x) = x := fun x => by
    rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hP), one_mulVec]
  have hform : ∀ y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (P *ᵥ y) (P *ᵥ y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal d) y y := fun y => by
    rw [herm_mulVec_mulVec', hPd]
  suffices ∃ y, y ≠ 0 ∧ _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal d) y y = 0 by
    obtain ⟨y, hy, hy0⟩ := this
    exact ⟨P *ᵥ y, fun h => hy (eq_zero_of_mulVec_eq_zero hP h), by rw [hf, hform, hy0]⟩
  by_cases hd0 : ∃ i, d i = 0
  · obtain ⟨i, hi⟩ := hd0
    refine ⟨Pi.single i 1, fun h => one_ne_zero (α := E) (by simpa using congr_fun h i), ?_⟩
    rw [_root_.GlobalTheory.UTrans.herm_diagonal_self, Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hj
      simp [Pi.single_apply, hj]
    · simp
  · push_neg at hd0
    refine _root_.GlobalTheory.UTrans.exists_isotropic_diagonal hn hd hd0 fun τ => ?_
    obtain ⟨⟨x, hx⟩, y, hy⟩ := hs τ
    rw [hf, ← hPinv x, hform] at hx
    rw [hf, ← hPinv y, hform] at hy
    exact ⟨exists_re_pos_of_herm_diagonal_re_pos τ d _ hx, exists_re_neg_of_herm_diagonal_re_neg τ d _ hy⟩

end GlobalTheory.UTrans
