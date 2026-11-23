import Mathlib
import Formalism.PeriodIntegrals.ExpTri
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.SortedSpec

open Matrix Finset
open scoped MatrixOrder ComplexOrder

noncomputable section

namespace PI.ET

namespace HornW

variable {n : ℕ}

lemma unit_star_mul {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ) :
    Wᴴ * W = 1 := by
  exact Unitary.star_mul_self_of_mem hW

lemma unit_mul_star {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ) :
    W * Wᴴ = 1 := by
  exact Unitary.mul_star_self_of_mem hW

lemma conj_mul_conj {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ)
    (d e : Fin n → ℂ) :
    (W * diagonal d * Wᴴ) * (W * diagonal e * Wᴴ) = W * diagonal (fun i => d i * e i) * Wᴴ := by
  calc (W * diagonal d * Wᴴ) * (W * diagonal e * Wᴴ)
      = W * (diagonal d * (Wᴴ * W) * diagonal e) * Wᴴ := by simp only [Matrix.mul_assoc]
    _ = W * diagonal (fun i => d i * e i) * Wᴴ := by
      rw [unit_star_mul hW, Matrix.mul_one, diagonal_mul_diagonal]

lemma conj_herm (W : Matrix (Fin n) (Fin n) ℂ) (r : Fin n → ℝ) :
    (W * diagonal (fun i => (r i : ℂ)) * Wᴴ)ᴴ = W * diagonal (fun i => (r i : ℂ)) * Wᴴ := by
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
    Matrix.mul_assoc]
  congr 3
  funext i
  simp

lemma exp_conj {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ) (d : Fin n → ℝ) :
    NormedSpace.exp (W * diagonal (fun i => (d i : ℂ)) * Wᴴ) =
      W * diagonal (fun i => (Real.exp (d i) : ℂ)) * Wᴴ := by
  have hinv : W⁻¹ = Wᴴ := Matrix.inv_eq_left_inv (unit_star_mul hW)
  have hu : IsUnit W :=
    (Matrix.isUnit_iff_isUnit_det W).mpr (Matrix.isUnit_det_of_right_inverse (unit_mul_star hW))
  rw [← hinv, Matrix.exp_conj W _ hu, Matrix.exp_diagonal, Pi.exp_def]
  congr 3
  funext i
  rw [Complex.ofReal_exp, Complex.exp_eq_exp_ℂ]

lemma sq_conj {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ) (d : Fin n → ℝ) :
    (W * diagonal (fun i => (Real.exp (d i) : ℂ)) * Wᴴ) *
        (W * diagonal (fun i => (Real.exp (d i) : ℂ)) * Wᴴ) =
      W * diagonal (fun i => (Real.exp (2 * d i) : ℂ)) * Wᴴ := by
  rw [conj_mul_conj hW]
  congr 3
  funext i
  simp only [two_mul, Real.exp_add, Complex.ofReal_mul]

lemma det_conj {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ) (d : Fin n → ℂ) :
    (W * diagonal d * Wᴴ).det = ∏ i, d i := by
  have h : W.det * Wᴴ.det = 1 := by rw [← Matrix.det_mul, unit_mul_star hW, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  linear_combination (∏ i, d i) * h

lemma norm_det_conj_exp {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ)
    (d : Fin n → ℝ) :
    ‖(W * diagonal (fun i => (Real.exp (d i) : ℂ)) * Wᴴ).det‖ = Real.exp (∑ i, d i) := by
  rw [det_conj hW, norm_prod, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

def emb {k : ℕ} (hk : k ≤ n) : Matrix (Fin n) (Fin k) ℂ :=
  Matrix.of fun i j => if i = Fin.castLE hk j then 1 else 0

lemma emb_compress {k : ℕ} (hk : k ≤ n) (f : Fin n → ℂ) :
    (emb hk)ᴴ * diagonal f * emb hk = diagonal (fun i => f (Fin.castLE hk i)) := by
  ext i j
  simp only [emb, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, diagonal_apply]
  simp [Finset.sum_ite_eq', Finset.sum_ite_eq, (Fin.castLE_injective hk).eq_iff]
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [h, h.symm]

lemma emb_isom {k : ℕ} (hk : k ≤ n) : (emb hk)ᴴ * emb hk = 1 := by
  have h := emb_compress hk (fun _ => 1)
  simpa [Matrix.diagonal_one] using h

lemma compress_conj {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ) {k : ℕ}
    (hk : k ≤ n) (f : Fin n → ℂ) :
    (W * emb hk)ᴴ * (W * diagonal f * Wᴴ) * (W * emb hk) =
      diagonal (fun i => f (Fin.castLE hk i)) := by
  rw [conjTranspose_mul]
  calc (emb hk)ᴴ * Wᴴ * (W * diagonal f * Wᴴ) * (W * emb hk)
      = (emb hk)ᴴ * ((Wᴴ * W) * diagonal f * (Wᴴ * W)) * emb hk := by simp only [Matrix.mul_assoc]
    _ = diagonal (fun i => f (Fin.castLE hk i)) := by
      rw [unit_star_mul hW, Matrix.one_mul, Matrix.mul_one, emb_compress]

lemma psum_eq {k : ℕ} (hk : k ≤ n) (f : Fin n → ℝ) :
    psum f k = ∑ i : Fin k, f (Fin.castLE hk i) := by
  unfold psum
  symm
  apply Finset.sum_nbij (fun i : Fin k => Fin.castLE hk i)
  · intro a _
    simp [a.isLt]
  · intro a _ b _ h
    exact Fin.castLE_injective hk h
  · intro b hb
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hb
    exact ⟨⟨b.val, hb⟩, by simp, Fin.ext (by simp)⟩
  · intro a _
    rfl

lemma psum_add (k : ℕ) (f g : Fin n → ℝ) :
    psum (fun i => f i + g i) k = psum f k + psum g k := by
  simp only [psum, Finset.sum_add_distrib]

lemma norm_det_diag_exp {k : ℕ} (hk : k ≤ n) (f : Fin n → ℝ) :
    ‖(diagonal (fun i : Fin k => (Real.exp (2 * f (Fin.castLE hk i)) : ℂ))).det‖ =
      Real.exp (2 * psum f k) := by
  rw [Matrix.det_diagonal, norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
  rw [psum_eq hk, Finset.mul_sum, Real.exp_sum]

lemma prod_exp_eq {k : ℕ} (hk : k ≤ n) (f : Fin n → ℝ) :
    ∏ i : Fin k, Real.exp (2 * f (Fin.castLE hk i)) = Real.exp (2 * psum f k) := by
  rw [psum_eq hk, Finset.mul_sum, Real.exp_sum]

lemma anti_exp {d : Fin n → ℝ} (hd : Antitone d) : Antitone (fun i => Real.exp (2 * d i)) :=
  fun i j hij => Real.exp_le_exp.mpr (by have := hd hij; linarith)

lemma isUnit_conj_exp {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ)
    (d : Fin n → ℝ) : IsUnit (W * diagonal (fun i => (Real.exp (d i) : ℂ)) * Wᴴ).det := by
  rw [det_conj hW]
  exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ =>
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')

private lemma key_lemma' {k : ℕ} (B : Matrix (Fin n) (Fin k) ℂ) (hB : Function.Injective B.mulVec) :
    ∃ (V : Matrix (Fin n) (Fin k) ℂ) (P : Matrix (Fin k) (Fin k) ℂ), Vᴴ * V = 1 ∧ B = V * P := by
  have hG : (Bᴴ * B).PosDef := Matrix.PosDef.conjTranspose_mul_self B hB
  have hspec := hG.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  have hU1 := Unitary.star_mul_self_of_mem hG.1.eigenvectorUnitary.2
  have hU2 := Unitary.mul_star_self_of_mem hG.1.eigenvectorUnitary.2
  simp only [Matrix.star_eq_conjTranspose] at hspec hU1 hU2
  have hg : ∀ i, 0 < hG.1.eigenvalues i := hG.eigenvalues_pos
  set U : Matrix (Fin k) (Fin k) ℂ := (hG.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) with hU
  set g := hG.1.eigenvalues with hgdef
  let s : Fin k → ℂ := fun i => (((Real.sqrt (g i))⁻¹ : ℝ) : ℂ)
  let t : Fin k → ℂ := fun i => ((Real.sqrt (g i) : ℝ) : ℂ)
  have hst : (fun i => s i * t i) = fun _ => (1 : ℂ) := by
    funext i
    simp only [s, t]
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (Real.sqrt_pos.mpr (hg i)).ne', Complex.ofReal_one]
  have hsgs : (fun i => star s i * (RCLike.ofReal ∘ g) i * s i) = fun _ => (1 : ℂ) := by
    funext i
    have hs := Real.sqrt_pos.mpr (hg i)
    have hsq : Real.sqrt (g i) * Real.sqrt (g i) = g i := Real.mul_self_sqrt (hg i).le
    simp only [s, Pi.star_apply, Function.comp_apply, Complex.star_def, Complex.conj_ofReal]
    have key : (Real.sqrt (g i))⁻¹ * g i * (Real.sqrt (g i))⁻¹ = 1 := by
      rw [mul_comm _ (g i), mul_assoc, ← mul_inv, hsq, mul_inv_cancel₀ (hg i).ne']
    show (((Real.sqrt (g i))⁻¹ : ℝ) : ℂ) * ((g i : ℝ) : ℂ) * (((Real.sqrt (g i))⁻¹ : ℝ) : ℂ) = 1
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, key, Complex.ofReal_one]
  refine ⟨B * U * diagonal s, diagonal t * Uᴴ, ?_, ?_⟩
  · rw [conjTranspose_mul, conjTranspose_mul]
    calc (diagonal s)ᴴ * (Uᴴ * Bᴴ) * (B * U * diagonal s)
        = (diagonal s)ᴴ * (Uᴴ * (Bᴴ * B) * U) * diagonal s := by simp only [Matrix.mul_assoc]
      _ = (diagonal s)ᴴ * ((Uᴴ * U) * diagonal (RCLike.ofReal ∘ g) * (Uᴴ * U)) * diagonal s := by
          rw [hspec]; simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hU1, Matrix.one_mul, Matrix.mul_one, diagonal_conjTranspose, diagonal_mul_diagonal,
            diagonal_mul_diagonal, hsgs, diagonal_one]
  · calc B = B * (U * Uᴴ) := by rw [hU2, Matrix.mul_one]
      _ = B * U * diagonal (fun i => s i * t i) * Uᴴ := by
          rw [hst, diagonal_one, Matrix.mul_one, Matrix.mul_assoc]
      _ = B * U * diagonal s * (diagonal t * Uᴴ) := by
          rw [← diagonal_mul_diagonal]; simp only [Matrix.mul_assoc]

private lemma inv_smul_apply_smul_eq_of_smul_mem (hK : KyFanDet) {k : ℕ} (hk : k ≤ n) {p : Fin n → ℝ} (hp : Antitone p)
    (hp0 : ∀ i, 0 < p i) {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin k) ℂ) (hB : Function.Injective B.mulVec) :
    ‖(Bᴴ * (W * diagonal (fun i => (p i : ℂ)) * Wᴴ) * B).det‖ ≤
      (∏ i : Fin k, p (Fin.castLE hk i)) * ‖(Bᴴ * B).det‖ := by
  obtain ⟨V, P, hV, rfl⟩ := key_lemma' B hB
  have h := hK n k hk p W V hp hp0 hW hV
  have e1 : (V * P)ᴴ * (W * diagonal (fun i => (p i : ℂ)) * Wᴴ) * (V * P) =
      Pᴴ * (Vᴴ * (W * diagonal (fun i => (p i : ℂ)) * Wᴴ) * V) * P := by
    rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
  have e2 : (V * P)ᴴ * (V * P) = Pᴴ * P := by
    rw [conjTranspose_mul]
    calc Pᴴ * Vᴴ * (V * P) = Pᴴ * (Vᴴ * V) * P := by simp only [Matrix.mul_assoc]
      _ = Pᴴ * P := by rw [hV, Matrix.mul_one]
  rw [e1, e2, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul, norm_mul]
  have h0 : 0 ≤ ‖Pᴴ.det‖ * ‖P.det‖ := by positivity
  calc ‖Pᴴ.det‖ * ‖(Vᴴ * (W * diagonal (fun i => (p i : ℂ)) * Wᴴ) * V).det‖ * ‖P.det‖
      = ‖(Vᴴ * (W * diagonal (fun i => (p i : ℂ)) * Wᴴ) * V).det‖ * (‖Pᴴ.det‖ * ‖P.det‖) := by ring
    _ ≤ (∏ i : Fin k, p (Fin.castLE hk i)) * (‖Pᴴ.det‖ * ‖P.det‖) :=
        mul_le_mul_of_nonneg_right h h0

private lemma key_lemma_3 {k : ℕ} {B : Matrix (Fin n) (Fin k) ℂ} (L : Matrix (Fin k) (Fin n) ℂ)
    (hL : L * B = 1) : Function.Injective B.mulVec := by
  intro x y hxy
  have h1 := congrArg L.mulVec hxy
  simp only [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec] at h1
  exact h1

lemma key (hK : KyFanDet) {Wx Wy Wz : Matrix (Fin n) (Fin n) ℂ}
    (hWx : Wx ∈ unitaryGroup (Fin n) ℂ) (hWy : Wy ∈ unitaryGroup (Fin n) ℂ)
    (hWz : Wz ∈ unitaryGroup (Fin n) ℂ) {ξ η ζ : Fin n → ℝ} (hξ : Antitone ξ) (hη : Antitone η)
    (hcc : (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) *
        (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) =
      (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) *
        ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) *
          (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ)) *
        (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ))
    (k : ℕ) (hk : k ≤ n) :
    psum ζ k ≤ psum (fun i => ξ i + η i) k := by
  have hV : (Wz * emb hk)ᴴ * (Wz * emb hk) = 1 := by
    rw [conjTranspose_mul]
    calc (emb hk)ᴴ * Wzᴴ * (Wz * emb hk) = (emb hk)ᴴ * (Wzᴴ * Wz) * emb hk := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [unit_star_mul hWz, Matrix.mul_one, emb_isom]
  have hinj : Function.Injective ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * (Wz * emb hk)).mulVec := by
    apply key_lemma_3 ((Wz * emb hk)ᴴ * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)⁻¹)
    calc (Wz * emb hk)ᴴ * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)⁻¹ * ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * (Wz * emb hk)) = (Wz * emb hk)ᴴ * ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)⁻¹ * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)) * (Wz * emb hk) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.nonsing_inv_mul _ (isUnit_conj_exp hWy η), Matrix.mul_one, hV]
  have hA : ‖((Wz * emb hk)ᴴ * ((Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) * (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ)) * (Wz * emb hk)).det‖ = Real.exp (2 * psum ζ k) := by
    rw [sq_conj hWz, compress_conj hWz hk, norm_det_diag_exp hk]
  rw [hcc] at hA
  have e1 : (Wz * emb hk)ᴴ * ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ)) * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)) * (Wz * emb hk) =
      ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * (Wz * emb hk))ᴴ * ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ)) * ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * (Wz * emb hk)) := by
    rw [conjTranspose_mul (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ), conj_herm]; simp only [Matrix.mul_assoc]
  rw [e1, sq_conj hWx] at hA
  have h2 := inv_smul_apply_smul_eq_of_smul_mem hK hk (anti_exp hξ) (fun i => Real.exp_pos _) hWx _ hinj
  rw [hA] at h2
  have e2 : ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * (Wz * emb hk))ᴴ * ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * (Wz * emb hk)) = (Wz * emb hk)ᴴ * ((Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)) * (Wz * emb hk) := by
    rw [conjTranspose_mul (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ), conj_herm]; simp only [Matrix.mul_assoc]
  rw [e2, sq_conj hWy] at h2
  have h3 := hK n k hk _ Wy (Wz * emb hk) (anti_exp hη) (fun i => Real.exp_pos _) hWy hV
  rw [prod_exp_eq hk] at h2
  rw [prod_exp_eq hk] at h3
  have h4 : Real.exp (2 * psum ζ k) ≤ Real.exp (2 * psum ξ k) * Real.exp (2 * psum η k) :=
    h2.trans (mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le)
  rw [← Real.exp_add, Real.exp_le_exp] at h4
  rw [psum_add]
  linarith

end HornW

open HornW in

theorem horn_of (hK : KyFanDet) : Horn := by
  intro n X Y Z U ξ η ζ hX hY hZ hU hE
  obtain ⟨hξ, Wx, hWx, rfl⟩ := hX
  obtain ⟨hη, Wy, hWy, rfl⟩ := hY
  obtain ⟨hζ, Wz, hWz, rfl⟩ := hZ
  rw [exp_conj hWx, exp_conj hWy, exp_conj hWz] at hE
  have hcc : (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) * (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) = (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ)) * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) := by
    have h1 : ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ))ᴴ * ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)) = (U * (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ))ᴴ * (U * (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ)) := by rw [hE]
    rw [conjTranspose_mul (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ), conjTranspose_mul U (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ), conj_herm, conj_herm, conj_herm] at h1
    calc (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) * (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) = (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) * (Uᴴ * U) * (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ) := by rw [unit_star_mul hU, Matrix.mul_one]
      _ = (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)) := by rw [h1]; simp only [Matrix.mul_assoc]
      _ = (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) * ((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ)) * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ) := by simp only [Matrix.mul_assoc]
  refine ⟨fun k hk => key hK hWx hWy hWz hξ hη hcc k hk, ?_⟩
  have hd : ‖((Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) * (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ)).det‖ = ‖(U * (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ)).det‖ := by rw [hE]
  have hUd : ‖U.det‖ = 1 := by
    have h2 : ‖star U.det * U.det‖ = 1 := by
      rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, unit_star_mul hU, Matrix.det_one, norm_one]
    rw [norm_mul, norm_star] at h2
    rcases mul_self_eq_one_iff.mp h2 with h | h
    · exact h
    · linarith [norm_nonneg U.det]
  rw [Matrix.det_mul (Wx * diagonal (fun i => (Real.exp (ξ i) : ℂ)) * Wxᴴ) (Wy * diagonal (fun i => (Real.exp (η i) : ℂ)) * Wyᴴ), Matrix.det_mul U (Wz * diagonal (fun i => (Real.exp (ζ i) : ℂ)) * Wzᴴ), norm_mul, norm_mul, norm_det_conj_exp hWx,
    norm_det_conj_exp hWy, norm_det_conj_exp hWz, hUd, one_mul, ← Real.exp_add] at hd
  rw [Finset.sum_add_distrib]
  exact (Real.exp_injective hd).symm

end PI.ET
