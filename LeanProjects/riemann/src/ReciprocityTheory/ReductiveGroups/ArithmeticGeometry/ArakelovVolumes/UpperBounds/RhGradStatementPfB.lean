import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustStatementPfB

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgC

open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD

variable {n : ℕ}

theorem leviV_const (c : ℝ) (x : V n) (ξ : Fin n → ℂ) :
    leviV n (fun _ => (c : ℂ)) x ξ = 0 := by
  have h : ∀ k, wdb n k (fun _ : V n => (c : ℂ)) = fun _ => 0 := by
    intro k; funext y; simp [wdb]
  simp [leviV, h, wd]

theorem quad_contDiff {r s : ℕ} (τ : ℝ) (ℓ : Fin r → Fin s → V n → ℂ)
    (hℓ : ∀ a b, ContDiff ℂ ∞ (ℓ a b)) :
    ContDiff ℝ ∞ (fun y => τ - ∑ a, ∑ b, Complex.normSq (ℓ a b y)) := by
  refine contDiff_const.sub (ContDiff.sum fun a _ => ContDiff.sum fun b _ => ?_)
  simp only [Complex.normSq_eq_norm_sq]
  exact (contDiff_norm_sq ℝ).comp ((hℓ a b).restrict_scalars ℝ)

theorem levi_quad_nonpos {r s : ℕ} (τ : ℝ) (ℓ : Fin r → Fin s → V n → ℂ)
    (hℓ : ∀ a b, ContDiff ℂ ∞ (ℓ a b)) (x : V n) (ξ : Fin n → ℂ) :
    (leviV n (fun y => ((τ - ∑ a, ∑ b, Complex.normSq (ℓ a b y) : ℝ) : ℂ)) x ξ).re ≤ 0 := by
  have hc : ∀ a b, ContDiffAt ℝ 2 (fun y => Complex.normSq (ℓ a b y)) x := by
    intro a b
    have h := quad_contDiff (r := 1) (s := 1) 0 (fun _ _ => ℓ a b) (fun _ _ => hℓ a b)
    have h2 : ContDiff ℝ ∞ (fun y => Complex.normSq (ℓ a b y)) := by
      have := h.neg
      simpa using this
    exact h2.contDiffAt.of_le (WithTop.coe_le_coe.2 le_top)
  have hca : ∀ a, ContDiffAt ℝ 2 (fun y => ∑ b, Complex.normSq (ℓ a b y)) x := fun a =>
    ContDiffAt.sum fun b _ => hc a b
  have hS : ContDiffAt ℝ 2 (fun y => ∑ a, ∑ b, Complex.normSq (ℓ a b y)) x :=
    ContDiffAt.sum fun a _ => hca a
  have e1 : (fun y => ((τ - ∑ a, ∑ b, Complex.normSq (ℓ a b y) : ℝ) : ℂ)) =
      fun y => ((τ + (-1) * ∑ a, ∑ b, Complex.normSq (ℓ a b y) : ℝ) : ℂ) := by
    funext y; push_cast; ring
  rw [e1, ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_add contDiffAt_const (contDiffAt_const.mul hS) ξ,
    leviV_const, ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul (-1) hS ξ,
    ReciprocityTheory.L2DbarEstimates.leviV_ofReal_sum hca ξ]
  simp only [ReciprocityTheory.L2DbarEstimates.leviV_ofReal_sum (fun b => hc _ b) ξ]
  simp only [ReciprocityTheory.L2DbarEstimates.H.leviV_normSq_comp ((hℓ _ _).contDiffAt.of_le (WithTop.coe_le_coe.2 le_top)) ξ]
  simp only [zero_add, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.re_sum,
    Complex.im_sum, zero_mul, sub_zero]
  have : 0 ≤ ∑ a : Fin r, ∑ b : Fin s, Complex.normSq (∑ j, wd n j (ℓ a b) x * ξ j) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _
  nlinarith

theorem trace_mul_conjTranspose_re {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℂ) :
    (B * Bᴴ).trace.re = ∑ a, ∑ b, Complex.normSq (B a b) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum,
    Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

theorem Q_formula {r s : ℕ} (Z : Matrix (Fin r) (Fin s) ℂ) (y : Matrix (Fin r) (Fin r) ℂ) :
    ((1 - Z * Zᴴ) * (yᴴ * y)).trace.re =
      (yᴴ * y).trace.re - ∑ a, ∑ b, Complex.normSq ((y * Z) a b) := by
  rw [← trace_mul_conjTranspose_re, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub,
    Complex.sub_re]
  congr 2
  rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem posDef_swap {r s : ℕ} {Z : Matrix (Fin r) (Fin s) ℂ} (h : (1 - Z * Zᴴ).PosDef) :
    (1 - Zᴴ * Z).PosDef := by
  have hu : IsUnit (1 - Z * Zᴴ).det := isUnit_iff_ne_zero.2 h.det_pos.ne'
  set S := (1 - Z * Zᴴ)⁻¹ with hS
  have hAS : (1 - Z * Zᴴ) * S = 1 := Matrix.mul_nonsing_inv _ hu
  have key : (1 - Zᴴ * Z) * (1 + Zᴴ * S * Z) = 1 := by
    have e : (1 - Zᴴ * Z) * (1 + Zᴴ * S * Z) = 1 + Zᴴ * ((1 - Z * Zᴴ) * S - 1) * Z := by
      simp only [Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.one_mul,
        Matrix.mul_one, Matrix.mul_assoc]
      abel
    rw [e, hAS, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero]
  have hinv : (1 - Zᴴ * Z)⁻¹ = 1 + Zᴴ * S * Z := Matrix.inv_eq_right_inv key
  have hP : (1 + Zᴴ * S * Z).PosDef :=
    PosDef.one.add_posSemidef ((h.inv).posSemidef.conjTranspose_mul_mul_same Z)
  rw [← hinv] at hP
  exact Matrix.posDef_inv_iff.1 hP

end ReciprocityTheory.ChartRestriction.G.AR.Up.RgC

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgD

open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.RgC

variable {f p q : ℕ}

theorem block (hm : 0 < min p q) {v0 : V (nD f p q)} (hv0 : v0 ∈ Dset f p q) (k : Fin f) :
    ∃ Q : V (nD f p q) → ℝ, ContDiff ℝ ∞ Q ∧
      (∀ ξ, (leviV (nD f p q) (fun y => (Q y : ℂ)) v0 ξ).re ≤ 0) ∧
      Q v0 = (min p q : ℕ) ∧
      ∀ v ∈ Dset f p q, dk v k ^ (((min p q : ℕ) : ℝ)⁻¹) ≤
        dk v0 k ^ (((min p q : ℕ) : ℝ)⁻¹) * (Q v / (min p q : ℕ)) := by
  rcases le_total p q with hpq | hqp
  · rw [min_eq_left hpq] at hm ⊢
    have hA0 := hv0 k
    obtain ⟨y, hy⟩ := RgB.exists_factor hA0.inv.posSemidef
    set Q : V (nD f p q) → ℝ := fun v =>
      ((1 - Zof v k * (Zof v k)ᴴ) * (1 - Zof v0 k * (Zof v0 k)ᴴ)⁻¹).trace.re with hQdef
    have hℓ : ∀ a b, ContDiff ℂ ∞ (fun v : V (nD f p q) => (y * Zof v k) a b) := by
      intro a b
      simp only [Matrix.mul_apply, Zof, Matrix.of_apply]
      exact ContDiff.sum fun c _ => contDiff_const.mul (cd_coord _)
    have hQ : Q = fun v => (yᴴ * y).trace.re -
        ∑ a, ∑ b, Complex.normSq ((fun a b (v : V (nD f p q)) => (y * Zof v k) a b) a b v) := by
      funext v; simp only [hQdef]; rw [hy, Q_formula]
    refine ⟨Q, ?_, ?_, ?_, ?_⟩
    · rw [hQ]; exact quad_contDiff _ _ hℓ
    · intro ξ; rw [hQ]; exact levi_quad_nonpos _ _ hℓ v0 ξ
    · simp only [hQdef]
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA0.det_pos.ne')]
      simp
    · intro v hv
      exact RgB.amgm hm (hv k) hA0
  · rw [min_eq_right hqp] at hm ⊢
    have hA0 := posDef_swap (hv0 k)
    obtain ⟨y, hy⟩ := RgB.exists_factor hA0.inv.posSemidef
    set Q : V (nD f p q) → ℝ := fun v =>
      ((1 - (Zof v k)ᴴ * Zof v k) * (1 - (Zof v0 k)ᴴ * Zof v0 k)⁻¹).trace.re with hQdef
    have hℓ : ∀ a b, ContDiff ℂ ∞
        (fun v : V (nD f p q) => ∑ c, star (y a c) * Zof v k b c) := by
      intro a b
      simp only [Zof, Matrix.of_apply]
      exact ContDiff.sum fun c _ => contDiff_const.mul (cd_coord _)
    have hQ : Q = fun v => (yᴴ * y).trace.re - ∑ a, ∑ b, Complex.normSq
        ((fun a b (v : V (nD f p q)) => ∑ c, star (y a c) * Zof v k b c) a b v) := by
      funext v
      simp only [hQdef]
      have h1 := Q_formula (Zof v k)ᴴ y
      rw [Matrix.conjTranspose_conjTranspose] at h1
      rw [hy, h1]
      congr 1
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [← Complex.normSq_conj]
      congr 1
      simp [Matrix.mul_apply, conjTranspose_apply, map_sum, Complex.star_def, mul_comm]
    refine ⟨Q, ?_, ?_, ?_, ?_⟩
    · rw [hQ]; exact quad_contDiff _ _ hℓ
    · intro ξ; rw [hQ]; exact levi_quad_nonpos _ _ hℓ v0 ξ
    · simp only [hQdef]
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA0.det_pos.ne')]
      simp
    · intro v hv
      have h := RgB.amgm hm (posDef_swap (hv k)) hA0
      simp only [dk]
      rw [Matrix.det_one_sub_mul_comm, Matrix.det_one_sub_mul_comm (Zof v0 k)]
      exact h

end ReciprocityTheory.ChartRestriction.G.AR.Up.RgD
