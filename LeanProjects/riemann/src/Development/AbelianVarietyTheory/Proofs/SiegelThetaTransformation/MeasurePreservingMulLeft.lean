import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralTransportHermitianFrameChartMeasure

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.Slab

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in

theorem _root_.GlobalTheory.SW.Slab.exists_lminor_near {r : ℕ} (S : Matrix (Fin r) (Fin r) ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ G : Matrix (Fin r) (Fin r) ℂ, (∀ a b, ‖G a b - S a b‖ < δ) →
      ∀ i, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.lminor G i - _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor S i‖ < 1 / 2 := by
  have hF : Continuous fun G : Fin r → Fin r → ℂ =>
      fun i : Fin (r + 1) => _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor (Matrix.of G) i := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor; fun_prop
  obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.mp hF (fun a b => S a b) (1 / 2) (by norm_num)
  refine ⟨min δ 1, lt_min hδ one_pos, min_le_right _ _, fun G hG i => ?_⟩
  have hd : dist (fun a b => G a b) (fun a b => S a b) < δ := by
    rw [dist_pi_lt_iff hδ]
    intro a
    rw [dist_pi_lt_iff hδ]
    intro b
    rw [dist_eq_norm]
    exact (hG a b).trans_le (min_le_left _ _)
  have h2 := (dist_pi_lt_iff (by norm_num : (0 : ℝ) < 1 / 2)).mp (h _ hd) i
  rw [dist_eq_norm] at h2
  exact h2

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in

theorem _root_.GlobalTheory.SW.Slab.exists_bound_upper {r : ℕ} (d : Fin r → ℂ) (hd : ∀ a, ‖d a‖ = 1) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : Matrix (Fin r) (Fin r) ℂ, b.BlockTriangular id → (∀ a, b a a ≠ 0) →
      (∀ a, ‖(b a a)⁻¹‖ ≤ 2) →
      (∀ a c, ‖(bᵀ * Matrix.diagonal d * b.map (starRingEnd ℂ)) a c‖ ≤ 2) →
      ∀ k : Fin r, (k : ℕ) < m → ∀ c, ‖b k c‖ ≤ C := by
  induction m with
  | zero => exact ⟨0, le_rfl, fun b _ _ _ _ k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨C, hC0, hC⟩ := ih
    refine ⟨2 * (2 + r * C ^ 2), by positivity, ?_⟩
    intro b hb hdiag hinv hM k hk c
    have hrow : ∀ j : Fin r, j < k → ∀ c, ‖b j c‖ ≤ C := fun j hj c' =>
      hC b hb hdiag hinv hM j (by have := Fin.lt_iff_val_lt_val.mp hj; omega) c'
    set f : Fin r → ℂ := fun j => b j k * d j * conj (b j c) with hf
    have hentry : (bᵀ * Matrix.diagonal d * b.map (starRingEnd ℂ)) k c = ∑ j, f j := by
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply, f]
    have hzero : ∀ j, k < j → f j = 0 := fun j hj => by
      simp [f, hb hj]
    have hsplit : ∑ j, f j = (∑ j ∈ Finset.univ.filter (· < k), f j) + f k := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· < k)]
      congr 1
      rw [Finset.sum_eq_single_of_mem k (by simp)]
      intro j hj hjk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
      exact hzero j (lt_of_le_of_ne hj (Ne.symm hjk))
    have hfk : ‖f k‖ = ‖b k k‖ * ‖b k c‖ := by
      simp [f, norm_mul, hd]
    have hsum : ‖∑ j ∈ Finset.univ.filter (· < k), f j‖ ≤ r * C ^ 2 := by
      calc ‖∑ j ∈ Finset.univ.filter (· < k), f j‖
          ≤ ∑ j ∈ Finset.univ.filter (· < k), ‖f j‖ := norm_sum_le _ _
        _ ≤ ∑ j ∈ Finset.univ.filter (· < k), C ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          simp only [f, norm_mul, hd, mul_one, RCLike.norm_conj]
          rw [sq]
          exact mul_le_mul (hrow j hj k) (hrow j hj c) (norm_nonneg _) hC0
        _ = (Finset.univ.filter (· < k)).card * C ^ 2 := by simp
        _ ≤ r * C ^ 2 := by
          gcongr
          exact (Finset.card_filter_le _ _).trans (by simp)
    have hfk_le : ‖b k k‖ * ‖b k c‖ ≤ 2 + r * C ^ 2 := by
      rw [← hfk]
      have : f k = (bᵀ * Matrix.diagonal d * b.map (starRingEnd ℂ)) k c -
          ∑ j ∈ Finset.univ.filter (· < k), f j := by
        rw [hentry, hsplit]; ring
      rw [this]
      exact (norm_sub_le _ _).trans (add_le_add (hM k c) hsum)
    have hkk : ‖(b k k)⁻¹‖ * ‖b k k‖ = 1 := by
      rw [norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hdiag k))]
    calc ‖b k c‖ = ‖(b k k)⁻¹‖ * (‖b k k‖ * ‖b k c‖) := by rw [← mul_assoc, hkk, one_mul]
      _ ≤ 2 * (2 + r * C ^ 2) :=
        mul_le_mul (hinv k) hfk_le (by positivity) (by norm_num)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
theorem _root_.GlobalTheory.SW.Slab.norm_sgn (p a : ℕ) : ‖((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn p a : ℝ) : ℂ)‖ = 1 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
  split_ifs <;> simp

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
theorem _root_.GlobalTheory.SW.Slab.psgn_sq (p i : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn p i = 1 ∨ _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn p i = -1 := by
  induction i with
  | zero => left; simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.psgn]
  | succ k ih =>
    rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.psgn_succ]
    rcases ih with h | h <;> rcases _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sgn_sq p k with h' | h' <;> simp [h, h']

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
theorem _root_.GlobalTheory.SW.Slab.lminor_sgnM (i : Fin (r + 1)) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor (_root_.GlobalTheory.SW.sgnM X) i = ((_root_.ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i : ℝ) : ℂ) := by
  unfold _root_.GlobalTheory.SW.sgnM
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_diagonal]
  simp only [Fin.coe_castLE]
  rw [Fin.prod_univ_eq_prod_range (fun a => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ)) i]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn
  push_cast
  rfl

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
private theorem gram_eq_transpose_mul_map_mul_conj' {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.gram, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
theorem _root_.GlobalTheory.SW.Slab.det_gram (τ : E →+* ℂ) (x : Matrix (Fin r) (Fin r) ℂ) :
    (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm x).det = x.det * τ X.Gm.det * conj x.det := by
  have h1 : (X.Gm.map τ).det = τ X.Gm.det := (RingHom.map_det τ X.Gm).symm
  have h2 : (x.map (starRingEnd ℂ)).det = conj x.det := (RingHom.map_det (starRingEnd ℂ) x).symm
  rw [gram_eq_transpose_mul_map_mul_conj', Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h1, h2]

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
theorem _root_.GlobalTheory.SW.Slab.continuous_gram (τ : X.Ψ) (a b : Fin r) :
    Continuous fun x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r => _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) a b := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.gram _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC _root_.ReciprocityTheory.ChartRestriction.G.FD.col _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
  simp only [Matrix.of_apply]
  fun_prop

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
theorem _root_.GlobalTheory.SW.Slab.gram_lmulC {u : X.Ψ → Matrix (Fin r) (Fin r) ℂ}
    (hu : ∀ (τ : X.Ψ) v w, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (u τ *ᵥ v) (u τ *ᵥ w) = _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm v w)
    (τ : X.Ψ) (x : Matrix (Fin r) (Fin r) ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (u τ * x) = _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm x := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.gram
  ext a b
  simp only [Matrix.of_apply, _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.col_mul, hu]

end GlobalTheory.SW.Slab

namespace GlobalTheory.SW

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
private theorem mem_slab_iff_norm_gram_sub_sgnM_lt {δ : ℝ} {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} :
    x ∈ _root_.GlobalTheory.SW.slab X δ ↔ ∀ (τ : X.Ψ) (a b : Fin r),
      ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) a b - _root_.GlobalTheory.SW.sgnM X a b‖ < δ :=
  Iff.rfl

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
private theorem mem_dom_iff_det_ne_zero_and_sign_dmin {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} :
    x ∈ X.dom ↔ ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i * (_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i).re :=
  Iff.rfl

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
private theorem sign_re_pos_and_norm_bounds_of_near_sign {z : ℂ} {s : ℝ} (hs : s = 1 ∨ s = -1)
    (h : ‖z - s‖ < 1 / 2) : 0 < s * z.re ∧ 1 / 2 < ‖z‖ ∧ ‖z‖ < 3 / 2 := by
  have hsn : ‖(s : ℂ)‖ = 1 := by rcases hs with rfl | rfl <;> simp
  have h1 : |z.re - s| < 1 / 2 := by
    have := Complex.abs_re_le_norm (z - s)
    rw [Complex.sub_re, Complex.ofReal_re] at this
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_lt] at h1
    rcases hs with rfl | rfl <;> linarith
  · have := norm_sub_norm_le (s : ℂ) z
    rw [norm_sub_rev] at this
    linarith
  · have := norm_sub_norm_le z (s : ℂ)
    linarith

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
private theorem lminor_last_eq_det {r : ℕ} (G : Matrix (Fin r) (Fin r) ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor G (Fin.last r) = G.det := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor; rfl

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
private theorem mem_Bor_iff_det_ne_zero_and_lower_eq_zero {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ}
    {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r} : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r ↔
      ∀ τ : Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0 := Iff.rfl

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
private theorem frame_ext_of_mat_eq' {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ}
    {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r} (h : ∀ τ, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ) : x = y :=
  funext fun τ => h τ

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
private theorem measurePreserving_mul_left_of_normSq_det_eq_one {r : ℕ} (u : Matrix (Fin r) (Fin r) ℂ)
    (hu : Complex.normSq u.det = 1) :
    MeasurePreserving (fun (M : Fin r → Fin r → ℂ) (i j : Fin r) => ∑ k, u i k * M k j)
      volume volume := by
  haveI : (volume : Measure (Fin r → Fin r → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ => (volume : Measure (Fin r → ℂ)))
  let L : (Fin r → Fin r → ℂ) →ₗ[ℂ] (Fin r → Fin r → ℂ) :=
    { toFun := fun M i j => ∑ k, u i k * M k j
      map_add' := fun M N => by
        funext i j
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c M => by
        funext i j
        simp [Finset.mul_sum, mul_left_comm] }
  let T : (Fin r → Fin r → ℂ) ≃ₗ[ℂ] (Fin r → Fin r → ℂ) :=
    { toFun := fun M i j => M j i
      invFun := fun M i j => M j i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hconj : T.toLinearMap ∘ₗ L ∘ₗ T.symm.toLinearMap =
      LinearMap.pi fun i => (Matrix.toLin' u) ∘ₗ LinearMap.proj i := by
    apply LinearMap.ext
    intro M
    funext i j
    simp [L, T, Matrix.mulVec, dotProduct]
  have hdetL : LinearMap.det L = u.det ^ r := by
    rw [← LinearMap.det_conj L T, hconj, LinearMap.det_pi]
    simp [LinearMap.det_toLin']
  have hdet : LinearMap.det (L.restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, hdetL, map_pow, Algebra.norm_complex_apply, hu, one_pow]
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (Fin r → Fin r → ℂ)) (f := L.restrictScalars ℝ) (by rw [hdet]; norm_num)
  rw [hdet] at hmap
  refine ⟨(L.restrictScalars ℝ).continuous_of_finiteDimensional.measurable, ?_⟩
  simp only [inv_one, abs_one, ENNReal.ofReal_one, one_smul] at hmap
  exact hmap

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
private theorem mat_lmulC' (u : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (τ : X.Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (X.lmulC u x) τ = u τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ := rfl

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
private theorem norm_sgnM_le_one (a b : Fin r) :
    ‖_root_.GlobalTheory.SW.sgnM X a b‖ ≤ 1 := by
  unfold _root_.GlobalTheory.SW.sgnM
  by_cases h : a = b
  · subst h
    rw [Matrix.diagonal_apply_eq, _root_.GlobalTheory.SW.Slab.norm_sgn]
  · rw [Matrix.diagonal_apply_ne _ h]
    simp

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in

theorem _root_.GlobalTheory.SW.thin_slab : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → IsOpen (_root_.GlobalTheory.SW.slab X δ) ∧ _root_.GlobalTheory.SW.slab X δ ⊆ X.dom ∧ (∀ x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, (∀ τ : X.Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = _root_.GlobalTheory.SW.sgnM X) → x ∈ _root_.GlobalTheory.SW.slab X δ) ∧ (∃ x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, (∀ τ : X.Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = _root_.GlobalTheory.SW.sgnM X)) ∧ (∀ u : X.Ψ → Matrix (Fin r) (Fin r) ℂ, (∀ (τ : X.Ψ) v w, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (u τ *ᵥ v) (u τ *ᵥ w) = _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm v w) → MeasurePreserving (X.lmulC u) volume volume ∧ (∀ x, X.lmulC u x ∈ _root_.GlobalTheory.SW.slab X δ ↔ x ∈ _root_.GlobalTheory.SW.slab X δ) ∧ ∀ x, X.lmulC u x ∈ X.dom ↔ x ∈ X.dom) ∧ (∃ C : ℝ, ∀ x ∈ _root_.GlobalTheory.SW.slab X δ, ∃ x' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, (∀ τ : X.Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' τ) = _root_.GlobalTheory.SW.sgnM X) ∧ ∃ b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r, x = _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x' b ∧ ∀ τ i j, ‖b τ i j‖ ≤ C ∧ ‖(b τ i i)⁻¹‖ ≤ C) ∧ ∀ x ∈ X.dom, ∃ x' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, (∀ τ : X.Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' τ) = _root_.GlobalTheory.SW.sgnM X) ∧ ∃ b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r, x = _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x' b := by
  intro E _ _ _ r X
  obtain ⟨δ₀, hδ₀, hδ₀1, hnear⟩ := _root_.GlobalTheory.SW.Slab.exists_lminor_near (_root_.GlobalTheory.SW.sgnM X)
  have hmin : ∀ δ, δ ≤ δ₀ → ∀ x ∈ _root_.GlobalTheory.SW.slab X δ, ∀ (τ : X.Ψ) (i : Fin (r + 1)),
      ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i - ((_root_.ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i : ℝ) : ℂ)‖ < 1 / 2 := by
    intro δ hδ x hx τ i
    rw [← _root_.GlobalTheory.SW.Slab.lminor_sgnM X i]
    exact hnear _ (fun a b => ((mem_slab_iff_norm_gram_sub_sgnM_lt X).mp hx τ a b).trans_le hδ) i
  have hdomS : ∀ δ, δ ≤ δ₀ → _root_.GlobalTheory.SW.slab X δ ⊆ X.dom := by
    intro δ hδ x hx
    rw [mem_dom_iff_det_ne_zero_and_sign_dmin]
    intro τ
    have hpos : ∀ i : Fin (r + 1), 0 < _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i * (_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i).re := fun i =>
      (sign_re_pos_and_norm_bounds_of_near_sign (_root_.GlobalTheory.SW.Slab.psgn_sq _ _)
        (hmin δ hδ x hx τ i)).1
    refine ⟨fun h0 => ?_, hpos⟩
    have hlast := hpos (Fin.last r)
    have hdg := _root_.GlobalTheory.SW.Slab.det_gram X τ.1 (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)
    have hzero : _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ (Fin.last r) = 0 := by
      show _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)) (Fin.last r) = 0
      rw [lminor_last_eq_det, hdg, h0]
      simp
    rw [hzero] at hlast
    simp at hlast
  have hin : ∀ δ, 0 < δ → ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, (∀ τ : X.Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) =
      _root_.GlobalTheory.SW.sgnM X) → x ∈ _root_.GlobalTheory.SW.slab X δ := by
    intro δ hδ x hx
    rw [mem_slab_iff_norm_gram_sub_sgnM_lt]
    intro τ a b
    rw [hx τ]
    simpa using hδ
  have hdecomp : ∀ x ∈ X.dom, ∃ x' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, (∀ τ : X.Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' τ) =
      _root_.GlobalTheory.SW.sgnM X) ∧ ∃ b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r, x = _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x' b := by
    intro x hx
    have hb := _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem X hx
    have hBdet : ∀ τ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).det ≠ 0 := fun τ =>
      ((mem_Bor_iff_det_ne_zero_and_lower_eq_zero).mp hb τ).1
    refine ⟨_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x), _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf X hx,
      fun τ => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ), ?_, ?_⟩
    · refine (mem_Bor_iff_det_ne_zero_and_lower_eq_zero).mpr ?_
      intro τ
      refine ⟨?_, fun a c hca => ?_⟩
      · show ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)⁻¹).det ≠ 0
        rw [Matrix.det_nonsing_inv]
        rw [Ring.inverse_eq_inv']
        exact inv_ne_zero (hBdet τ)
      · haveI : Invertible (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ) :=
          Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr (hBdet τ))
        have ht := Matrix.blockTriangular_inv_of_blockTriangular (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.upper_of_bor X hb τ)
        exact ht hca
    · apply frame_ext_of_mat_eq'
      intro τ
      show _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ *
        ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hBdet τ)),
        Matrix.mul_one]
  obtain ⟨C₀, -, hbound⟩ := _root_.GlobalTheory.SW.Slab.exists_bound_upper (fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ))
    (fun a => _root_.GlobalTheory.SW.Slab.norm_sgn _ _) r
  refine ⟨δ₀, hδ₀, fun δ hδ hδle => ⟨?_, hdomS δ hδle, hin δ hδ,
    ⟨fun τ => (X.signature τ).choose, fun τ => (X.signature τ).choose_spec.2⟩, ?_, ?_, hdecomp⟩⟩
  · have hset : _root_.GlobalTheory.SW.slab X δ = ⋂ τ : X.Ψ, ⋂ a : Fin r, ⋂ b : Fin r,
        {x | ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) a b - _root_.GlobalTheory.SW.sgnM X a b‖ < δ} := by
      ext x
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      exact mem_slab_iff_norm_gram_sub_sgnM_lt X
    rw [hset]
    exact isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a =>
      isOpen_iInter_of_finite fun b =>
        isOpen_lt ((_root_.GlobalTheory.SW.Slab.continuous_gram X τ a b).sub continuous_const).norm
          continuous_const
  · intro u hu
    have hdet : ∀ τ, Complex.normSq (u τ).det = 1 := by
      intro τ
      have h := _root_.GlobalTheory.SW.Slab.gram_lmulC X hu τ 1
      rw [Matrix.mul_one] at h
      have h2 := congrArg Matrix.det h
      rw [_root_.GlobalTheory.SW.Slab.det_gram, _root_.GlobalTheory.SW.Slab.det_gram, Matrix.det_one,
        map_one, one_mul, mul_one] at h2
      have hG : (τ.1 : E →+* ℂ) X.Gm.det ≠ 0 := (map_ne_zero _).mpr X.Gm_det
      have h3 : (u τ).det * conj (u τ).det = 1 := by
        apply mul_right_cancel₀ hG
        linear_combination h2
      rw [Complex.mul_conj] at h3
      exact_mod_cast h3
    have hne : ∀ τ, (u τ).det ≠ 0 := fun τ h => by
      have := hdet τ
      rw [h, map_zero] at this
      norm_num at this
    refine ⟨?_, fun x => ?_, fun x => ?_⟩
    · have hp := measurePreserving_pi (fun _ : X.Ψ => (volume : Measure (Fin r → Fin r → ℂ)))
        (fun _ => volume) (fun τ => measurePreserving_mul_left_of_normSq_det_eq_one (u τ) (hdet τ))
      have heq : (X.lmulC u) = fun (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (τ : X.Ψ) (i j : Fin r) =>
          ∑ k, u τ i k * x τ k j := by
        funext x τ i j
        rfl
      rw [heq]
      exact hp
    · rw [mem_slab_iff_norm_gram_sub_sgnM_lt, mem_slab_iff_norm_gram_sub_sgnM_lt]
      simp only [mat_lmulC', _root_.GlobalTheory.SW.Slab.gram_lmulC X hu]
    · rw [mem_dom_iff_det_ne_zero_and_sign_dmin, mem_dom_iff_det_ne_zero_and_sign_dmin]
      simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin, mat_lmulC', _root_.GlobalTheory.SW.Slab.gram_lmulC X hu, Matrix.det_mul]
      simp [hne]
  · refine ⟨max C₀ 2, fun x hx => ?_⟩
    obtain ⟨y, hy, b, hb, rfl⟩ := hdecomp x (hdomS δ hδle hx)
    refine ⟨y, hy, b, hb, rfl, ?_⟩
    have hydom : y ∈ X.dom := hdomS δ₀ le_rfl (hin δ₀ hδ₀ y hy)
    intro τ
    have hbt := _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.upper_of_bor X hb τ
    have hdiag : ∀ a, b τ a a ≠ 0 := fun a => _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bdiag_ne X hb τ a
    have hgram : _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul y b) τ) = (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ)ᵀ *
        Matrix.diagonal (fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ)) *
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).map (starRingEnd ℂ) := by
      show _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ) = _
      rw [_root_.GlobalTheory.FlagTransport.gram_mul_right, hy τ]
      rfl
    have hM : ∀ a c, ‖((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ)ᵀ * Matrix.diagonal (fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ)) *
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).map (starRingEnd ℂ)) a c‖ ≤ 2 := by
      intro a c
      rw [← hgram]
      have h1 := (mem_slab_iff_norm_gram_sub_sgnM_lt X).mp hx τ a c
      have h2 := norm_sgnM_le_one X a c
      have h3 := norm_add_le (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul y b) τ) a c -
        _root_.GlobalTheory.SW.sgnM X a c) (_root_.GlobalTheory.SW.sgnM X a c)
      rw [sub_add_cancel] at h3
      linarith
    have hPy : ∀ i : Fin (r + 1), _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm y τ i = ((_root_.ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i : ℝ) : ℂ) := fun i => by
      show _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ)) i = _
      rw [hy τ, _root_.GlobalTheory.SW.Slab.lminor_sgnM]
    have hnorm1 : ∀ i : ℕ, ‖((_root_.ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i : ℝ) : ℂ)‖ = 1 := fun i => by
      rcases _root_.GlobalTheory.SW.Slab.psgn_sq X.p0 i with h | h <;> simp [h]
    have hinv : ∀ k, ‖(b τ k k)⁻¹‖ ≤ 2 := by
      intro k
      have hr := _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ratio_rmul X y hydom hb τ k
      simp only [hPy, norm_div, hnorm1, div_one, mul_one] at hr
      obtain ⟨-, hs1, -⟩ := sign_re_pos_and_norm_bounds_of_near_sign
        (_root_.GlobalTheory.SW.Slab.psgn_sq _ _) (hmin δ hδle _ hx τ k.succ)
      obtain ⟨-, hc1, hc2⟩ := sign_re_pos_and_norm_bounds_of_near_sign
        (_root_.GlobalTheory.SW.Slab.psgn_sq _ _) (hmin δ hδle _ hx τ k.castSucc)
      have htpos : 0 < ‖b τ k k‖ := norm_pos_iff.mpr (hdiag k)
      have ht : 1 / 3 < ‖b τ k k‖ ^ 2 := by
        rw [← hr, lt_div_iff₀ (by linarith)]
        linarith
      rw [norm_inv, inv_le_comm₀ htpos (by norm_num)]
      nlinarith
    intro i j
    exact ⟨(hbound (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ) hbt hdiag hinv hM i i.isLt j).trans (le_max_left _ _),
      (hinv i).trans (le_max_right _ _)⟩

end GlobalTheory.SW
