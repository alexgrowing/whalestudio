import Mathlib

open Matrix
open scoped ComplexOrder

namespace Formalism.L2.Geo.Rec.TraceQuadraticBound

variable {n : Type} [Fintype n] [DecidableEq n]

theorem exists_star_mul_self {A : Matrix n n ℂ} (hA : A.PosSemidef) : ∃ B : Matrix n n ℂ, A = Bᴴ * B := by
  open scoped MatrixOrder in
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  exact ⟨B, hB⟩

theorem frame_exists {A : Matrix n n ℂ} (hA : A.PosSemidef) (hd : A.det ≠ 0) :
    ∃ X : Matrix n n ℂ, X * Xᴴ = A ∧ IsUnit X.det := by
  obtain ⟨B, rfl⟩ := exists_star_mul_self hA
  refine ⟨Bᴴ, by rw [conjTranspose_conjTranspose], ?_⟩
  rw [det_mul] at hd
  exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul hd)

theorem re_star_dot_self (v : n → ℂ) : (star v ⬝ᵥ v).re = ∑ i, ‖v i‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

theorem norm_sum_sq_le (a w : n → ℂ) : ‖∑ k, a k * w k‖ ^ 2 ≤ (∑ k, ‖a k‖ ^ 2) * ∑ k, ‖w k‖ ^ 2 := by
  have h1 : ‖∑ k, a k * w k‖ ≤ ∑ k, ‖a k‖ * ‖w k‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => norm_mul _ _))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖a k‖) (fun k => ‖w k‖)
  have h0 : 0 ≤ ‖∑ k, a k * w k‖ := norm_nonneg _
  calc ‖∑ k, a k * w k‖ ^ 2 ≤ (∑ k, ‖a k‖ * ‖w k‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ _ := h2

theorem quad_le_trace_HH (H : Matrix n n ℂ) (w : n → ℂ) :
    (star w ⬝ᵥ (Hᴴ * H) *ᵥ w).re ≤ (Hᴴ * H).trace.re * ∑ i, ‖w i‖ ^ 2 := by
  have e1 : star w ⬝ᵥ (Hᴴ * H) *ᵥ w = star (H *ᵥ w) ⬝ᵥ (H *ᵥ w) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, star_mulVec]
  rw [e1, re_star_dot_self]
  have e2 : (Hᴴ * H).trace.re = ∑ j, ∑ k, ‖H k j‖ ^ 2 := by
    simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.conj_mul']; norm_cast
  rw [e2, Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  exact norm_sum_sq_le (fun j => H k j) w

theorem quad_le_trace {b : Matrix n n ℂ} (hb : b.PosSemidef) (Y : Matrix n n ℂ) (w : n → ℂ) :
    (star (Y *ᵥ w) ⬝ᵥ b *ᵥ (Y *ᵥ w)).re ≤ (b * (Y * Yᴴ)).trace.re * ∑ i, ‖w i‖ ^ 2 := by
  obtain ⟨H, hH⟩ := exists_star_mul_self (hb.conjTranspose_mul_mul_same Y)
  have e1 : star (Y *ᵥ w) ⬝ᵥ b *ᵥ (Y *ᵥ w) = star w ⬝ᵥ (Yᴴ * b * Y) *ᵥ w := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have e2 : (b * (Y * Yᴴ)).trace = (Yᴴ * b * Y).trace := by
    rw [← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  rw [e1, e2, hH]
  exact quad_le_trace_HH H w

theorem trace_nonneg {b : Matrix n n ℂ} (hb : b.PosSemidef) (Y : Matrix n n ℂ) :
    0 ≤ (b * (Y * Yᴴ)).trace.re := by
  obtain ⟨H, hH⟩ := exists_star_mul_self (hb.conjTranspose_mul_mul_same Y)
  have e2 : (b * (Y * Yᴴ)).trace = (Yᴴ * b * Y).trace := by
    rw [← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  rw [e2, hH]
  simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_
  rw [Complex.star_def, Complex.conj_mul']; norm_cast; positivity

theorem trace_pos {b : Matrix n n ℂ} (hb : b.PosSemidef) (hb0 : b ≠ 0) (Y : Matrix n n ℂ)
    (hY : IsUnit Y.det) : 0 < (b * (Y * Yᴴ)).trace.re := by
  obtain ⟨H, hH⟩ := exists_star_mul_self (hb.conjTranspose_mul_mul_same Y)
  have e2 : (b * (Y * Yᴴ)).trace = (Yᴴ * b * Y).trace := by
    rw [← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  have e3 : (Hᴴ * H).trace.re = ∑ j, ∑ k, ‖H k j‖ ^ 2 := by
    simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.conj_mul']; norm_cast
  rw [e2, hH, e3]
  by_contra hle
  have hs : ∑ j, ∑ k, ‖H k j‖ ^ 2 = 0 :=
    le_antisymm (not_lt.mp hle) (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => by positivity)
  have hH0 : H = 0 := by
    ext k j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Finset.sum_nonneg fun k _ => by positivity)).1 hs j
      (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).1 h1 k (Finset.mem_univ _)
    simpa using h2
  apply hb0
  have hYi : IsUnit Yᴴ.det := by rw [det_conjTranspose]; exact hY.star
  have hz : Yᴴ * b * Y = 0 := by rw [hH, hH0]; simp
  calc b = (Yᴴ⁻¹ * Yᴴ) * b * (Y * Y⁻¹) := by
        rw [Matrix.nonsing_inv_mul _ hYi, Matrix.mul_nonsing_inv _ hY]; simp
    _ = Yᴴ⁻¹ * (Yᴴ * b * Y) * Y⁻¹ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hz]; simp

section Dense

variable {K : Type} [Field K]

theorem denseRange_emb (σ : K →+* ℂ) (z : K) (hz : (σ z).im ≠ 0) : DenseRange σ := by
  let g : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (p.2 : ℂ) * σ z
  have hg : Continuous g := by fun_prop
  have hgs : Function.Surjective g := by
    intro w
    refine ⟨(w.re - w.im / (σ z).im * (σ z).re, w.im / (σ z).im), ?_⟩
    apply Complex.ext
    · simp [g]
    · simp [g]; field_simp
  have hq : DenseRange (Prod.map (fun q : ℚ => (q : ℝ)) (fun q : ℚ => (q : ℝ))) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have h := hgs.denseRange.comp hq hg
  refine h.mono ?_
  rintro _ ⟨⟨a, b⟩, rfl⟩
  exact ⟨(a : K) + (b : K) * z, by simp [g]⟩

theorem psd_map {m : ℕ} (cj : K → K) (σ : K →+* ℂ) (hσ : ∀ z, σ (cj z) = star (σ z)) (hd : DenseRange σ)
    (A : Matrix (Fin m) (Fin m) K) (hH : ∀ i k, A k i = cj (A i k))
    (hP : ∀ l : Fin m → K, l ≠ 0 → 0 < (σ (∑ i, ∑ k, l i * A i k * cj (l k))).re) :
    (A.map σ).PosSemidef ∧ (A.map σ).det ≠ 0 := by
  have hHm : (A.map σ).IsHermitian := by
    ext i k
    simp only [conjTranspose_apply, map_apply]
    rw [hH, hσ, star_star]
  have key : ∀ l : Fin m → K, σ (∑ i, ∑ k, l i * A i k * cj (l k)) =
      star (fun k => star (σ (l k))) ⬝ᵥ (A.map σ) *ᵥ (fun k => star (σ (l k))) := by
    intro l
    simp only [map_sum, map_mul, hσ, dotProduct, mulVec, map_apply, Pi.star_apply, star_star, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have hden : DenseRange (fun l : Fin m → K => fun k => star (σ (l k))) := by
    have h1 : DenseRange (fun z : K => star (σ z)) :=
      (Function.RightInverse.surjective (f := (star : ℂ → ℂ)) (g := star) star_star).denseRange.comp hd
        continuous_star
    exact DenseRange.piMap (f := fun _ : Fin m => fun z : K => star (σ z)) (fun _ => h1)
  have hre : ∀ x : Fin m → ℂ, 0 ≤ (star x ⬝ᵥ (A.map σ) *ᵥ x).re := by
    intro x
    refine hden.induction_on (p := fun x => 0 ≤ (star x ⬝ᵥ (A.map σ) *ᵥ x).re) x ?_ ?_
    · apply isClosed_le continuous_const
      simp only [dotProduct, mulVec, Pi.star_apply]
      fun_prop
    · intro l
      show 0 ≤ (star (fun k => star (σ (l k))) ⬝ᵥ (A.map σ) *ᵥ (fun k => star (σ (l k)))).re
      by_cases hl : l = 0
      · subst hl
        rw [show (fun k : Fin m => star (σ ((0 : Fin m → K) k))) = 0 by funext k; simp]
        simp
      · rw [← key]; exact (hP l hl).le
  refine ⟨PosSemidef.of_dotProduct_mulVec_nonneg hHm fun x => ?_, ?_⟩
  · rw [Complex.nonneg_iff]
    exact ⟨hre x, (hHm.im_star_dotProduct_mulVec_self x).symm⟩
  · rw [show (A.map σ).det = σ A.det from (RingHom.map_det σ A).symm]
    intro h0
    apply (map_eq_zero_iff σ σ.injective).not.mpr ?_ h0
    intro hdet
    obtain ⟨l, hl, hlA⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    have := hP l hl
    have e : ∑ i, ∑ k, l i * A i k * cj (l k) = ∑ k, (l ᵥ* A) k * cj (l k) := by
      simp only [vecMul, dotProduct, Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [e, hlA] at this
    simp at this

end Dense

end Formalism.L2.Geo.Rec.TraceQuadraticBound

open NumberField NumberField.InfinitePlace

namespace Formalism.L2.Geo.Rec.TraceSumEmbeddings

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]

end Formalism.L2.Geo.Rec.TraceSumEmbeddings
