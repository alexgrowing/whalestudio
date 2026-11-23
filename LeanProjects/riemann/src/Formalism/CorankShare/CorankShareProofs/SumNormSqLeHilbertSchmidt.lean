import Mathlib
import Formalism.CorankShare.StatementFR

noncomputable section

namespace Formalism.CorankShareLayerCake.FR

namespace Pgsn2pfrla

open Finset Module LinearMap
open scoped InnerProductSpace

section gen
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

lemma norm_inner_swap (x y : E) : ‖⟪x, y⟫_ℂ‖ = ‖⟪y, x⟫_ℂ‖ := by
  exact norm_inner_symm x y

private lemma re_inner_self_eq_norm_sq_corank_share {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] (x : G) :
    (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 :=
  inner_self_eq_norm_sq (𝕜 := ℂ) x

private lemma orthonormalBasis_sum_norm_inner_sq_eq_norm_sq {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ G) (x : G) : ∑ i, ‖⟪b i, x⟫_ℂ‖ ^ 2 = ‖x‖ ^ 2 :=
  b.sum_sq_norm_inner_right x

lemma sum_adj_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (A : E →ₗ[ℂ] F)
    (v : OrthonormalBasis ι ℂ E) (u : OrthonormalBasis κ ℂ F) :
    ∑ n, ‖adjoint A (u n)‖ ^ 2 = ∑ m, ‖A (v m)‖ ^ 2 := by
  have h1 : ∀ n, ‖adjoint A (u n)‖ ^ 2 = ∑ m, ‖⟪u n, A (v m)⟫_ℂ‖ ^ 2 := by
    intro n
    rw [← orthonormalBasis_sum_norm_inner_sq_eq_norm_sq v]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [LinearMap.adjoint_inner_right, norm_inner_swap]
  have h2 : ∀ m, ‖A (v m)‖ ^ 2 = ∑ n, ‖⟪u n, A (v m)⟫_ℂ‖ ^ 2 := fun m => (orthonormalBasis_sum_norm_inner_sq_eq_norm_sq u _).symm
  simp only [h1, h2]
  exact Finset.sum_comm

private lemma trace_eq_sum_inner_orthonormalBasis {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℂ E)
    (T : E →ₗ[ℂ] E) : trace ℂ E T = ∑ i, ⟪b i, T (b i)⟫_ℂ := by
  rw [LinearMap.trace_eq_matrix_trace ℂ b.toBasis, Matrix.trace]
  simp [LinearMap.toMatrix_apply, OrthonormalBasis.repr_apply_apply]

lemma hilbert_schmidt_eq_basis_sum {ι : Type*} [Fintype ι] (A : E →ₗ[ℂ] F) (v : OrthonormalBasis ι ℂ E) :
    hs2 A = ∑ m, ‖A (v m)‖ ^ 2 := by
  classical
  unfold hs2
  rw [trace_eq_sum_inner_orthonormalBasis v, Complex.re_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, re_inner_self_eq_norm_sq_corank_share]

lemma hilbert_schmidt_nonneg_alt (A : E →ₗ[ℂ] F) : 0 ≤ hs2 A := by
  rw [hilbert_schmidt_eq_basis_sum A (stdOrthonormalBasis ℂ E)]
  positivity

lemma sum_norm_sq_le_hilbert_schmidt {κ : Type*} [Fintype κ] (A : E →ₗ[ℂ] F) {g : κ → E} (hg : Orthonormal ℂ g) :
    ∑ l, ‖A (g l)‖ ^ 2 ≤ hs2 A := by
  rw [hilbert_schmidt_eq_basis_sum A (stdOrthonormalBasis ℂ E), ← sum_adj_eq A (stdOrthonormalBasis ℂ E) (stdOrthonormalBasis ℂ F)]
  have h1 : ∀ l, ‖A (g l)‖ ^ 2 = ∑ n, ‖⟪g l, adjoint A (stdOrthonormalBasis ℂ F n)⟫_ℂ‖ ^ 2 := by
    intro l
    rw [← orthonormalBasis_sum_norm_inner_sq_eq_norm_sq (stdOrthonormalBasis ℂ F)]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [LinearMap.adjoint_inner_right, norm_inner_swap]
  simp only [h1]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun n _ => Orthonormal.sum_inner_products_le _ hg)

lemma sum_re_inner_bound {κ : Type*} [Fintype κ] (A : E →ₗ[ℂ] E) {g : κ → E}
    (hg : Orthonormal ℂ g) :
    |∑ l, (⟪g l, A (g l)⟫_ℂ).re| ≤ Real.sqrt (Fintype.card κ) * Real.sqrt (hs2 A) := by
  have h1 : ∀ l, |(⟪g l, A (g l)⟫_ℂ).re| ≤ ‖A (g l)‖ := by
    intro l
    calc |(⟪g l, A (g l)⟫_ℂ).re| ≤ ‖⟪g l, A (g l)⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖g l‖ * ‖A (g l)‖ := norm_inner_le_norm _ _
      _ = ‖A (g l)‖ := by rw [hg.1 l, one_mul]
  have h2 : (∑ l, ‖A (g l)‖) ^ 2 ≤ (Fintype.card κ) * hs2 A := by
    have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun l => ‖A (g l)‖)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h3
    exact h3.trans (mul_le_mul_of_nonneg_left (sum_norm_sq_le_hilbert_schmidt A hg) (Nat.cast_nonneg _))
  calc |∑ l, (⟪g l, A (g l)⟫_ℂ).re| ≤ ∑ l, |(⟪g l, A (g l)⟫_ℂ).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, ‖A (g l)‖ := Finset.sum_le_sum (fun l _ => h1 l)
    _ = √((∑ l, ‖A (g l)‖) ^ 2) := (Real.sqrt_sq (Finset.sum_nonneg (fun l _ => norm_nonneg _))).symm
    _ ≤ √((Fintype.card κ) * hs2 A) := Real.sqrt_le_sqrt h2
    _ = √(Fintype.card κ) * √(hs2 A) := Real.sqrt_mul (Nat.cast_nonneg _) _

lemma fam_bound (c : ℝ) (B : E →ₗ[ℂ] F) {κ : Type*} [Fintype κ] {g : κ → E}
    (hg : Orthonormal ℂ g) :
    |c * ∑ l, ‖B (g l)‖ ^ 2 - Fintype.card κ|
      ≤ Real.sqrt (Fintype.card κ) * Real.sqrt (hs2 (frK c B - LinearMap.id)) := by
  have h1 : ∀ l, (⟪g l, ((frK c B - LinearMap.id : E →ₗ[ℂ] E)) (g l)⟫_ℂ).re = c * ‖B (g l)‖ ^ 2 - 1 := by
    intro l
    simp only [frK, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply,
      inner_sub_right, inner_smul_right, LinearMap.adjoint_inner_right, Complex.sub_re, Complex.re_ofReal_mul,
      re_inner_self_eq_norm_sq_corank_share, hg.1 l]
    norm_num
  have h2 : ∑ l, (⟪g l, ((frK c B - LinearMap.id : E →ₗ[ℂ] E)) (g l)⟫_ℂ).re = c * ∑ l, ‖B (g l)‖ ^ 2 - Fintype.card κ := by
    rw [Finset.sum_congr rfl (fun l _ => h1 l), Finset.sum_sub_distrib, Finset.mul_sum]
    simp
  rw [← h2]
  exact sum_re_inner_bound _ hg

end gen

section fam
variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
    [∀ i, InnerProductSpace ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

lemma re_inner_Q (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) (x : H) :
    (⟪x, frQ c B x⟫_ℂ).re = ∑ i, c i * ‖adjoint (B i) x‖ ^ 2 := by
  simp only [frQ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    inner_sum, inner_smul_right, Complex.re_sum, Complex.re_ofReal_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← LinearMap.adjoint_inner_left (B i) (adjoint (B i) x) x, re_inner_self_eq_norm_sq_corank_share]

lemma Q_symm (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) (x y : H) :
    ⟪frQ c B x, y⟫_ℂ = ⟪x, frQ c B y⟫_ℂ := by
  simp only [frQ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    sum_inner, inner_sum, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_left]

lemma tQ_eq (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) :
    (trace ℂ H (frQ c B)).re = ∑ i, c i * ∑ m, ‖B i (stdOrthonormalBasis ℂ (V i) m)‖ ^ 2 := by
  simp only [frQ, map_sum, map_smul, smul_eq_mul, Complex.re_sum, Complex.re_ofReal_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  rw [← hilbert_schmidt_eq_basis_sum (B i) (stdOrthonormalBasis ℂ (V i))]
  unfold hs2
  rw [LinearMap.trace_comp_comm']

lemma trace_frame_sq_eq_sum (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) :
    (trace ℂ H (frQ c B ∘ₗ frQ c B)).re = ∑ n, ‖frQ c B (stdOrthonormalBasis ℂ H n)‖ ^ 2 := by
  have hadj : frQ c B = adjoint (frQ c B) := by
    rw [LinearMap.eq_adjoint_iff]; exact Q_symm c B
  have h := hilbert_schmidt_eq_basis_sum (frQ c B) (stdOrthonormalBasis ℂ H)
  unfold hs2 at h
  rw [← hadj] at h
  exact h

lemma hilbert_schmidt_sub_scalar (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) (lam : ℝ) :
    hs2 (frQ c B - (lam : ℂ) • LinearMap.id) =
      (trace ℂ H (frQ c B ∘ₗ frQ c B)).re - 2 * lam * (trace ℂ H (frQ c B)).re
        + lam ^ 2 * finrank ℂ H := by
  have hadj : frQ c B - (lam : ℂ) • LinearMap.id = adjoint (frQ c B - (lam : ℂ) • LinearMap.id) := by
    rw [LinearMap.eq_adjoint_iff]
    intro x y
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal, Q_symm c B x y]
  unfold hs2
  rw [← hadj]
  simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp,
    LinearMap.comp_id, map_sub, map_smul, LinearMap.trace_id, smul_eq_mul, Complex.sub_re, Complex.re_ofReal_mul,
    Complex.natCast_re]
  ring

end fam

section wup
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

lemma W_upper (B : V →ₗ[ℂ] H) (N : Submodule ℂ V) {κ : Type*} [Fintype κ] {g : κ → H}
    (hg : Orthonormal ℂ g) (hperp : ∀ l, ∀ n ∈ N, ⟪B n, g l⟫_ℂ = 0) :
    ∑ l, ‖adjoint B (g l)‖ ^ 2 ≤ ∑ m, ‖B ((stdOrthonormalBasis ℂ Nᗮ m : V))‖ ^ 2 := by
  have hmem : ∀ l, adjoint B (g l) ∈ Nᗮ := by
    intro l
    rw [Submodule.mem_orthogonal]
    intro n hn
    rw [LinearMap.adjoint_inner_right, hperp l n hn]
  have h1 : ∀ l, ‖adjoint B (g l)‖ ^ 2 = ∑ m, ‖⟪g l, B ((stdOrthonormalBasis ℂ Nᗮ m : V))⟫_ℂ‖ ^ 2 := by
    intro l
    have h := orthonormalBasis_sum_norm_inner_sq_eq_norm_sq (stdOrthonormalBasis ℂ Nᗮ) ⟨adjoint B (g l), hmem l⟩
    have hn : ‖(⟨adjoint B (g l), hmem l⟩ : Nᗮ)‖ = ‖adjoint B (g l)‖ := rfl
    rw [hn] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have hi : ⟪stdOrthonormalBasis ℂ Nᗮ m, (⟨adjoint B (g l), hmem l⟩ : Nᗮ)⟫_ℂ
        = ⟪(stdOrthonormalBasis ℂ Nᗮ m : V), adjoint B (g l)⟫_ℂ := rfl
    rw [hi, LinearMap.adjoint_inner_right, norm_inner_swap]
  simp only [h1]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun m _ => Orthonormal.sum_inner_products_le _ hg)

end wup

lemma final_real (D R w e ε η t X tW : ℝ) (hD : 0 < D) (hR : 0 < R) (he0 : 0 ≤ e) (he : e ≤ 1/4)
    (hε : 0 ≤ ε) (hw0 : 0 ≤ w) (hwD : w ≤ D) (ht : R * (1 - √e) ≤ t) (hX0 : 0 ≤ X)
    (hX : X ≤ η * t ^ 2 / D) (hlow : t / D * w - √w * √X ≤ tW)
    (hup : tW ≤ ε * R + R * √(ε * e)) : w ≤ (2 * η + 4 * ε + 4 * √e) * D := by
  have hs0 : 0 ≤ √e := Real.sqrt_nonneg e
  have hs : √e ≤ 1 / 2 := by
    have h4 : √(1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [← h4]
    exact Real.sqrt_le_sqrt he
  have ht0 : R / 2 ≤ t := by nlinarith
  have htpos : 0 < t := by linarith
  have hXD : X * D ≤ η * t ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hX hD.le
    rwa [div_mul_cancel₀ _ hD.ne'] at h1
  have hη : 0 ≤ η := by
    have h2 : 0 ≤ η * t ^ 2 := le_trans (mul_nonneg hX0 hD.le) hXD
    by_contra hc
    push_neg at hc
    have : η * t ^ 2 < 0 := mul_neg_of_neg_of_pos hc (by positivity)
    linarith
  by_cases hK : 1 ≤ 2 * η + 4 * ε + 4 * √e
  · calc w ≤ D := hwD
      _ = 1 * D := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hK hD.le
  push_neg at hK
  have hε1 : ε ≤ 1 := by linarith
  have hsε : √ε ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hε1
  have hse : √(ε * e) = √ε * √e := Real.sqrt_mul hε e
  have hab : √w * √X * D ≤ t * (w + η * D) / 2 := by
    have hP : 0 ≤ √w * √X * D := by positivity
    have hQ : 0 ≤ t * (w + η * D) / 2 := by positivity
    have hsq : (√w * √X * D) ^ 2 ≤ (t * (w + η * D) / 2) ^ 2 := by
      have e1 : (√w * √X * D) ^ 2 = w * (X * D) * D := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hw0, Real.sq_sqrt hX0]; ring
      rw [e1]
      nlinarith [mul_le_mul_of_nonneg_left hXD (mul_nonneg hw0 hD.le),
        mul_nonneg (sq_nonneg t) (sq_nonneg (w - η * D))]
    calc √w * √X * D = √((√w * √X * D) ^ 2) := (Real.sqrt_sq hP).symm
      _ ≤ √((t * (w + η * D) / 2) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = t * (w + η * D) / 2 := Real.sqrt_sq hQ
  have hc := hlow.trans hup
  rw [hse] at hc
  have key : t * w - √w * √X * D ≤ D * (ε * R + R * (√ε * √e)) := by
    have h1 := mul_le_mul_of_nonneg_right hc hD.le
    have e1 : t / D * w * D = t * w := by field_simp
    nlinarith
  by_cases hwη : w ≤ η * D
  · nlinarith [mul_nonneg (by positivity : 0 ≤ η + 4 * ε + 4 * √e) hD.le]
  push_neg at hwη
  have h3 : R / 2 * (w - η * D) ≤ t * (w - η * D) := mul_le_mul_of_nonneg_right ht0 (by linarith)
  have h4 : R * ((w - η * D) - 4 * D * (ε + √ε * √e)) ≤ 0 := by nlinarith
  have h5 : (w - η * D) - 4 * D * (ε + √ε * √e) ≤ 0 := by
    by_contra hc2
    push_neg at hc2
    have := mul_pos hR hc2
    linarith
  have h6 : √ε * √e ≤ √e := mul_le_of_le_one_left hs0 hsε
  nlinarith [mul_le_mul_of_nonneg_left h6 hD.le, mul_nonneg hη hD.le]

end Pgsn2pfrla

open Finset Module LinearMap Pgsn2pfrla
open scoped InnerProductSpace

private lemma sum_sqrt_mul_sqrt_le_sqrt_sum_mul {ι : Type*} [Fintype ι] (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, 0 ≤ b i) : ∑ i, √(a i) * √(b i) ≤ √(∑ i, a i) * √(∑ i, b i) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => √(a i)) (fun i => √(b i))
  have e1 : ∀ i, √(a i) ^ 2 = a i := fun i => Real.sq_sqrt (ha i)
  have e2 : ∀ i, √(b i) ^ 2 = b i := fun i => Real.sq_sqrt (hb i)
  simp only [e1, e2] at h
  have hs : 0 ≤ ∑ i, √(a i) * √(b i) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  calc ∑ i, √(a i) * √(b i) = √((∑ i, √(a i) * √(b i)) ^ 2) := (Real.sqrt_sq hs).symm
    _ ≤ √((∑ i, a i) * ∑ i, b i) := Real.sqrt_le_sqrt h
    _ = √(∑ i, a i) * √(∑ i, b i) := Real.sqrt_mul (Finset.sum_nonneg (fun i _ => ha i)) _

theorem frame_linear_algebra_bound : FrameLA := by
  intro ι _ V _ _ _ H _ _ _ B c Nτ e η ε hc hR hF2 he0 he hF1 hcor
  classical
  have hRpos : 0 < (∑ i, (finrank ℂ (V i) : ℝ)) := by exact_mod_cast hR
  have hs0 : 0 ≤ √e := Real.sqrt_nonneg e
  have hs : √e ≤ 1 / 2 := by
    have h4 : √(1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [← h4]
    exact Real.sqrt_le_sqrt he
  have hh0 : ∀ i, 0 ≤ hs2 (frK (c i) (B i) - LinearMap.id) := fun i => hilbert_schmidt_nonneg_alt _

  have hlowi : ∀ i, (finrank ℂ (V i) : ℝ) - √(finrank ℂ (V i) : ℝ) * √(hs2 (frK (c i) (B i) - LinearMap.id))
      ≤ c i * ∑ m, ‖B i (stdOrthonormalBasis ℂ (V i) m)‖ ^ 2 := by
    intro i
    have h1 := fam_bound (c i) (B i) (stdOrthonormalBasis ℂ (V i)).orthonormal
    rw [Fintype.card_fin] at h1
    have h2 := (abs_le.mp h1).1
    linarith
  have ht : (∑ i, (finrank ℂ (V i) : ℝ)) * (1 - √e) ≤ (LinearMap.trace ℂ H (frQ c B)).re := by
    rw [tQ_eq c B]
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hlowi i)
    rw [Finset.sum_sub_distrib] at hsum
    have hcs := sum_sqrt_mul_sqrt_le_sqrt_sum_mul (fun i => (finrank ℂ (V i) : ℝ)) (fun i => hs2 (frK (c i) (B i) - LinearMap.id))
      (fun i => Nat.cast_nonneg _) hh0
    have h2 : √(∑ i, hs2 (frK (c i) (B i) - LinearMap.id)) ≤ √e * √(∑ i, (finrank ℂ (V i) : ℝ)) := by
      rw [← Real.sqrt_mul he0]
      exact Real.sqrt_le_sqrt hF2
    have h3 : √(∑ i, (finrank ℂ (V i) : ℝ)) * √(∑ i, (finrank ℂ (V i) : ℝ)) = (∑ i, (finrank ℂ (V i) : ℝ)) := Real.mul_self_sqrt hRpos.le
    have h4 : √(∑ i, (finrank ℂ (V i) : ℝ)) * √(∑ i, hs2 (frK (c i) (B i) - LinearMap.id)) ≤ (∑ i, (finrank ℂ (V i) : ℝ)) * √e := by
      calc √(∑ i, (finrank ℂ (V i) : ℝ)) * √(∑ i, hs2 (frK (c i) (B i) - LinearMap.id)) ≤ √(∑ i, (finrank ℂ (V i) : ℝ)) * (√e * √(∑ i, (finrank ℂ (V i) : ℝ))) :=
            mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
        _ = √e * (√(∑ i, (finrank ℂ (V i) : ℝ)) * √(∑ i, (finrank ℂ (V i) : ℝ))) := by ring
        _ = (∑ i, (finrank ℂ (V i) : ℝ)) * √e := by rw [h3]; ring
    linarith
  have hDpos : 0 < (finrank ℂ H : ℝ) := by
    rcases Nat.eq_zero_or_pos (finrank ℂ H) with h0 | h0
    · exfalso
      haveI : Subsingleton H := Module.finrank_zero_iff.mp h0
      have hQ0 : frQ c B = 0 := LinearMap.ext (fun x => Subsingleton.elim _ _)
      have h5 : (LinearMap.trace ℂ H (frQ c B)).re = 0 := by rw [hQ0, map_zero, Complex.zero_re]
      nlinarith
    · exact_mod_cast h0

  have hk : ∀ i, ((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) = (finrank ℂ (Nτ i)ᗮ : ℝ) := by
    intro i
    have h1 := Submodule.finrank_add_finrank_orthogonal (Nτ i)
    rw [← h1]
    push_cast
    ring
  have hk' : ∑ i, (finrank ℂ (Nτ i)ᗮ : ℝ) ≤ ε * (∑ i, (finrank ℂ (V i) : ℝ)) := by
    rw [← Finset.sum_congr rfl (fun i _ => hk i)]
    exact hcor
  have hε : 0 ≤ ε := by
    have h1 : 0 ≤ ∑ i, (finrank ℂ (Nτ i)ᗮ : ℝ) := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
    by_contra hc2
    push_neg at hc2
    have := mul_neg_of_neg_of_pos hc2 hRpos
    linarith

  obtain ⟨g, hgdef⟩ : ∃ g : Fin (finrank ℂ (⨆ i, (Nτ i).map (B i))ᗮ) → H,
      g = fun l => ((stdOrthonormalBasis ℂ (⨆ i, (Nτ i).map (B i))ᗮ l : (⨆ i, (Nτ i).map (B i))ᗮ) : H) := ⟨_, rfl⟩
  have hg : Orthonormal ℂ g := by
    rw [hgdef]
    exact (stdOrthonormalBasis ℂ (⨆ i, (Nτ i).map (B i))ᗮ).orthonormal.comp_linearIsometry (⨆ i, (Nτ i).map (B i))ᗮ.subtypeₗᵢ
  have hgW : ∀ l, g l ∈ (⨆ i, (Nτ i).map (B i))ᗮ := by
    intro l
    rw [hgdef]
    exact (stdOrthonormalBasis ℂ (⨆ i, (Nτ i).map (B i))ᗮ l).2
  have hperp : ∀ i, ∀ l, ∀ n ∈ Nτ i, ⟪B i n, g l⟫_ℂ = 0 := by
    intro i l n hn
    exact Submodule.inner_right_of_mem_orthogonal
      (Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem hn)) (hgW l)

  have htW : (∑ l, (⟪g l, frQ c B (g l)⟫_ℂ).re) = ∑ i, c i * ∑ l, ‖adjoint (B i) (g l)‖ ^ 2 := by
    rw [Finset.sum_congr rfl (fun l _ => re_inner_Q c B (g l)), Finset.sum_comm]
    simp only [Finset.mul_sum]
  have hupi : ∀ i, c i * ∑ l, ‖adjoint (B i) (g l)‖ ^ 2
      ≤ (finrank ℂ (Nτ i)ᗮ : ℝ) + √(finrank ℂ (Nτ i)ᗮ : ℝ) * √(hs2 (frK (c i) (B i) - LinearMap.id)) := by
    intro i
    have h1 := W_upper (B i) (Nτ i) hg (hperp i)
    have ho : Orthonormal ℂ (fun m => ((stdOrthonormalBasis ℂ (Nτ i)ᗮ m : (Nτ i)ᗮ) : V i)) :=
      (stdOrthonormalBasis ℂ (Nτ i)ᗮ).orthonormal.comp_linearIsometry (Nτ i)ᗮ.subtypeₗᵢ
    have h2 := fam_bound (c i) (B i) ho
    rw [Fintype.card_fin] at h2
    beta_reduce at h2
    have h3 := (abs_le.mp h2).2
    have h4 := mul_le_mul_of_nonneg_left h1 (hc i).le
    linarith
  have hup : (∑ l, (⟪g l, frQ c B (g l)⟫_ℂ).re) ≤ ε * (∑ i, (finrank ℂ (V i) : ℝ)) + (∑ i, (finrank ℂ (V i) : ℝ)) * √(ε * e) := by
    rw [htW]
    have hs1 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hupi i)
    rw [Finset.sum_add_distrib] at hs1
    have hcs := sum_sqrt_mul_sqrt_le_sqrt_sum_mul (fun i => (finrank ℂ (Nτ i)ᗮ : ℝ)) (fun i => hs2 (frK (c i) (B i) - LinearMap.id))
      (fun i => Nat.cast_nonneg _) hh0
    have h2 : √(∑ i, (finrank ℂ (Nτ i)ᗮ : ℝ)) * √(∑ i, hs2 (frK (c i) (B i) - LinearMap.id)) ≤ (∑ i, (finrank ℂ (V i) : ℝ)) * √(ε * e) := by
      calc √(∑ i, (finrank ℂ (Nτ i)ᗮ : ℝ)) * √(∑ i, hs2 (frK (c i) (B i) - LinearMap.id)) ≤ √(ε * (∑ i, (finrank ℂ (V i) : ℝ))) * √(e * (∑ i, (finrank ℂ (V i) : ℝ))) :=
            mul_le_mul (Real.sqrt_le_sqrt hk') (Real.sqrt_le_sqrt hF2) (Real.sqrt_nonneg _)
              (Real.sqrt_nonneg _)
        _ = √((ε * e) * ((∑ i, (finrank ℂ (V i) : ℝ)) * (∑ i, (finrank ℂ (V i) : ℝ)))) := by
            rw [← Real.sqrt_mul (mul_nonneg hε hRpos.le)]
            congr 1
            ring
        _ = (∑ i, (finrank ℂ (V i) : ℝ)) * √(ε * e) := by
            rw [Real.sqrt_mul (mul_nonneg hε he0), Real.sqrt_mul_self hRpos.le]
            ring
    linarith

  have hlow : (LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) * (finrank ℂ (⨆ i, (Nτ i).map (B i))ᗮ : ℝ) - √(finrank ℂ (⨆ i, (Nτ i).map (B i))ᗮ : ℝ) * √(hs2 (frQ c B - (((LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) : ℝ) : ℂ) • LinearMap.id)) ≤ (∑ l, (⟪g l, frQ c B (g l)⟫_ℂ).re) := by
    have hb := sum_re_inner_bound (frQ c B - (((LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) : ℝ) : ℂ) • LinearMap.id) hg
    rw [Fintype.card_fin] at hb
    have h1 : ∀ l, (⟪g l, g l⟫_ℂ).re = 1 := fun l => by rw [re_inner_self_eq_norm_sq_corank_share, hg.1 l]; norm_num
    have hsplit : ∑ l, (⟪g l, ((frQ c B - (((LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) : ℝ) : ℂ) • LinearMap.id : H →ₗ[ℂ] H)) (g l)⟫_ℂ).re
        = (∑ l, (⟪g l, frQ c B (g l)⟫_ℂ).re) - (LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) * (finrank ℂ (⨆ i, (Nτ i).map (B i))ᗮ : ℝ) := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, inner_sub_right,
        inner_smul_right, Complex.sub_re, Complex.re_ofReal_mul, Finset.sum_sub_distrib, h1, mul_one,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [hsplit] at hb
    have h2 := (abs_le.mp hb).1
    linarith
  have hX : hs2 (frQ c B - (((LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) : ℝ) : ℂ) • LinearMap.id) ≤ η * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) := by
    rw [hilbert_schmidt_sub_scalar c B ((LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ))]
    have e2 : ((LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ)) ^ 2 * (finrank ℂ H : ℝ) = (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) := by
      field_simp
    have e3 : (1 + η) * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) = (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) + η * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) := by ring
    have e4 : 2 * ((LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ)) * (LinearMap.trace ℂ H (frQ c B)).re = 2 * ((LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ)) := by ring
    linarith
  have hwD : (finrank ℂ (⨆ i, (Nτ i).map (B i))ᗮ : ℝ) ≤ (finrank ℂ H : ℝ) := by exact_mod_cast Submodule.finrank_le (⨆ i, (Nτ i).map (B i))ᗮ
  exact final_real (finrank ℂ H : ℝ) (∑ i, (finrank ℂ (V i) : ℝ)) (finrank ℂ (⨆ i, (Nτ i).map (B i))ᗮ : ℝ) e ε η (LinearMap.trace ℂ H (frQ c B)).re (hs2 (frQ c B - (((LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) : ℝ) : ℂ) • LinearMap.id)) (∑ l, (⟪g l, frQ c B (g l)⟫_ℂ).re) hDpos hRpos he0 he hε (Nat.cast_nonneg _) hwD ht
    (hilbert_schmidt_nonneg_alt _) hX hlow hup

end Formalism.CorankShareLayerCake.FR
