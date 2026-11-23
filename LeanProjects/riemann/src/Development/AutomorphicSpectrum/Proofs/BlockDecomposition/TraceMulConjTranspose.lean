import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.SuppBound

variable {n : ℕ}

def fr (N : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ a, ∑ b, ‖N a b‖ ^ 2

theorem fr_nonneg (N : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ fr N := by
  unfold fr
  positivity

theorem fr_conjTranspose (N : Matrix (Fin n) (Fin n) ℂ) : fr Nᴴ = fr N := by
  unfold fr
  rw [Finset.sum_comm]
  simp [conjTranspose_apply, norm_star]

theorem trace_mul_conjTranspose (N : Matrix (Fin n) (Fin n) ℂ) : (N * Nᴴ).trace = (fr N : ℂ) := by
  simp only [fr, Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Complex.star_def,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem sq_sum_le (N : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    ∑ i, ‖(Nᴴ *ᵥ v) i‖ ^ 2 ≤ fr N * ∑ j, ‖v j‖ ^ 2 := by
  have key : ∀ i, ‖(Nᴴ *ᵥ v) i‖ ^ 2 ≤ (∑ j, ‖N j i‖ ^ 2) * ∑ j, ‖v j‖ ^ 2 := by
    intro i
    have h1 : ‖(Nᴴ *ᵥ v) i‖ ≤ ∑ j, ‖N j i‖ * ‖v j‖ := by
      simp only [mulVec, dotProduct, conjTranspose_apply]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      simp [norm_star]
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖N j i‖) (fun j => ‖v j‖)
    calc ‖(Nᴴ *ᵥ v) i‖ ^ 2 ≤ (∑ j, ‖N j i‖ * ‖v j‖) ^ 2 := by gcongr
      _ ≤ _ := h2
  calc ∑ i, ‖(Nᴴ *ᵥ v) i‖ ^ 2 ≤ ∑ i, (∑ j, ‖N j i‖ ^ 2) * ∑ j, ‖v j‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => key i
    _ = fr N * ∑ j, ‖v j‖ ^ 2 := by rw [← Finset.sum_mul, fr, Finset.sum_comm]

theorem star_dot_self (w : Fin n → ℂ) : star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
  push_cast
  rfl

theorem psd_fr (N : Matrix (Fin n) (Fin n) ℂ) : (fr N • (1 : Matrix (Fin n) (Fin n) ℂ) - N * Nᴴ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine IsHermitian.sub ?_ (isHermitian_mul_conjTranspose_self N)
    simp [IsHermitian, conjTranspose_smul]
  · have e1 : star x ⬝ᵥ ((N * Nᴴ) *ᵥ x) = ((∑ i, ‖(Nᴴ *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) := by
      rw [← mulVec_mulVec, dotProduct_mulVec, ← star_dot_self, star_mulVec, conjTranspose_conjTranspose]
    have e2 : star x ⬝ᵥ ((fr N • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ x) = ((fr N * ∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) := by
      rw [show (fr N • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ x = (fr N : ℂ) • x by
        ext i; simp [mulVec, dotProduct, Matrix.one_apply, Complex.real_smul]]
      rw [dotProduct_smul, star_dot_self, smul_eq_mul]
      push_cast
      ring
    rw [sub_mulVec, dotProduct_sub, e1, e2, ← Complex.ofReal_sub, Complex.zero_le_real, sub_nonneg]
    exact sq_sum_le N x

theorem psd_conj {A B : Matrix (Fin n) (Fin n) ℂ} (h : (B - A).PosSemidef) (W : Matrix (Fin n) (Fin n) ℂ) :
    (W * B * Wᴴ - W * A * Wᴴ).PosSemidef := by
  have e : W * B * Wᴴ - W * A * Wᴴ = W * (B - A) * Wᴴ := by
    rw [mul_sub, sub_mul]
  rw [e]
  exact h.mul_mul_conjTranspose_same W

theorem psd_trace {A B : Matrix (Fin n) (Fin n) ℂ} (h : (B - A).PosSemidef) : A.trace.re ≤ B.trace.re := by
  have h0 := h.trace_nonneg
  rw [trace_sub] at h0
  have := (Complex.le_def.1 h0).1
  simp only [Complex.zero_re, Complex.sub_re] at this
  linarith

theorem psd_rsmul {A : Matrix (Fin n) (Fin n) ℂ} (h : A.PosSemidef) {t : ℝ} (ht : 0 ≤ t) : (t • A).PosSemidef := by
  exact h.smul ht

theorem psd_sandwich {N W : Matrix (Fin n) (Fin n) ℂ} {M : ℝ} (hM : fr N ≤ M) :
    (M • (W * Wᴴ) - (W * N) * (W * N)ᴴ).PosSemidef := by
  have h0 : ((M • (1 : Matrix (Fin n) (Fin n) ℂ)) - N * Nᴴ).PosSemidef := by
    have e : (M • (1 : Matrix (Fin n) (Fin n) ℂ)) - N * Nᴴ =
        (M - fr N) • (1 : Matrix (Fin n) (Fin n) ℂ) + (fr N • (1 : Matrix (Fin n) (Fin n) ℂ) - N * Nᴴ) := by
      rw [sub_smul]; abel
    rw [e]
    exact (psd_rsmul Matrix.PosSemidef.one (sub_nonneg.2 hM)).add (psd_fr N)
  have h1 := psd_conj h0 W
  have e : M • (W * Wᴴ) - (W * N) * (W * N)ᴴ = W * (M • (1 : Matrix (Fin n) (Fin n) ℂ)) * Wᴴ - W * (N * Nᴴ) * Wᴴ := by
    rw [conjTranspose_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    simp only [mul_assoc]
  rw [e]
  exact h1

section Frobenius

attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

theorem norm_sq_eq (N : Matrix (Fin n) (Fin n) ℂ) : ‖N‖ ^ 2 = fr N := by
  rw [frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp only [fr, Real.rpow_two]

theorem norm_le_sqrt {N : Matrix (Fin n) (Fin n) ℂ} {B : ℝ} (h : fr N ≤ B) : ‖N‖ ≤ √B := by
  have := Real.abs_le_sqrt (x := ‖N‖) (y := B) (by rw [norm_sq_eq]; exact h)
  rwa [abs_of_nonneg (norm_nonneg _)] at this

theorem entry_le (N : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) : ‖N a b‖ ≤ ‖N‖ := by
  have h : ‖N a b‖ ^ 2 ≤ ‖N‖ ^ 2 := by
    rw [norm_sq_eq]
    unfold fr
    calc ‖N a b‖ ^ 2 ≤ ∑ b', ‖N a b'‖ ^ 2 :=
          Finset.single_le_sum (f := fun b' => ‖N a b'‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ b)
      _ ≤ ∑ a', ∑ b', ‖N a' b'‖ ^ 2 :=
          Finset.single_le_sum (f := fun a' => ∑ b', ‖N a' b'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ a)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem pow_conj {y yi : Matrix (Fin n) (Fin n) ℂ} (h1 : y * yi = 1) (h2 : yi * y = 1)
    (D : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) : (yi * D * y) ^ k = yi * D ^ k * y := by
  induction k with
  | zero => simp [h2]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc]
    rw [← mul_assoc y yi, h1, one_mul]

theorem poly_conj {y yi : Matrix (Fin n) (Fin n) ℂ} (h1 : y * yi = 1) (h2 : yi * y = 1)
    (p : Polynomial ℂ) (w : Fin n → ℂ) :
    ∑ i ∈ range (p.natDegree + 1), p.coeff i • (yi * diagonal w * y) ^ i =
      yi * diagonal (fun b => p.eval (w b)) * y := by
  have hd : diagonal (fun b => p.eval (w b)) =
      ∑ i ∈ range (p.natDegree + 1), p.coeff i • diagonal (w ^ i) := by
    ext a b
    rw [Matrix.sum_apply]
    by_cases hab : a = b
    · subst hab
      simp [Polynomial.eval_eq_sum_range]
    · simp [hab]
  simp_rw [pow_conj h1 h2, diagonal_pow]
  rw [hd, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem norm_pow_bound {g : Matrix (Fin n) (Fin n) ℂ} {b : ℝ} (hb : ‖g‖ ≤ b) (k : ℕ) :
    ‖g ^ k‖ ≤ ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ * b ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hb0 : 0 ≤ b := (norm_nonneg _).trans hb
    calc ‖g ^ (k + 1)‖ = ‖g ^ k * g‖ := by rw [pow_succ]
      _ ≤ ‖g ^ k‖ * ‖g‖ := norm_mul_le _ _
      _ ≤ (‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ * b ^ k) * b :=
          mul_le_mul ih hb (norm_nonneg _) (by positivity)
      _ = _ := by rw [pow_succ, mul_assoc]

theorem norm_poly_bound (p : Polynomial ℂ) {g : Matrix (Fin n) (Fin n) ℂ} {b : ℝ} (hb : ‖g‖ ≤ b) :
    ‖∑ i ∈ range (p.natDegree + 1), p.coeff i • g ^ i‖ ≤
      ∑ i ∈ range (p.natDegree + 1), ‖p.coeff i‖ * (‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ * b ^ i) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_pow_bound hb i) (norm_nonneg _))

theorem entry_single (u : Matrix (Fin n) (Fin n) ℂ) (a i : Fin n) (c : ℂ) :
    (u * diagonal (fun b => if b = a then c else 0) * uᴴ) i i = c * (‖u i a‖ ^ 2 : ℝ) := by
  rw [Matrix.mul_apply]
  simp only [mul_diagonal, conjTranspose_apply]
  rw [Finset.sum_eq_single a]
  · simp only [if_pos rfl]
    rw [if_pos trivial]
    have := Complex.mul_conj (u i a)
    rw [Complex.normSq_eq_norm_sq] at this
    rw [Complex.star_def]
    linear_combination c * this
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ a) h

private theorem cancel_lemma {a b : Matrix (Fin n) (Fin n) ℂ} (h : a * b = 1) (X : Matrix (Fin n) (Fin n) ℂ) :
    a * (b * X) = X := by
  rw [← mul_assoc, h, one_mul]

theorem bounded_of_conj (z : Fin n → ℂ) (hz : ∀ a, ‖z a‖ = 1) (hinj : Function.Injective fun a => z a ^ 2) (B : ℝ) :
    ∃ C : ℝ, ∀ y yi : Matrix (Fin n) (Fin n) ℂ, y * yi = 1 → yi * y = 1 →
      fr (yi * diagonal z * yiᴴ) ≤ B → fr (yᴴ * (diagonal z)ᴴ * y) ≤ B → fr y ≤ C ∧ fr yi ≤ C := by
  classical
  let w : Fin n → ℂ := fun b => z b ^ 2
  have hinjw : Set.InjOn w ((Finset.univ : Finset (Fin n)) : Set (Fin n)) := fun a _ b _ h => hinj h
  let L : Fin n → Polynomial ℂ := fun a => Lagrange.basis Finset.univ w a
  let K : Fin n → ℝ := fun a =>
    ∑ i ∈ range ((L a).natDegree + 1), ‖(L a).coeff i‖ * (‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ * B ^ i)
  refine ⟨n * ∑ a, K a * √B, ?_⟩
  intro y yi h1 h2 hA hN
  have hB : 0 ≤ B := (fr_nonneg _).trans hA
  have hy1' : yiᴴ * yᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have c7 := cancel_lemma hy1'
  have c3 := cancel_lemma h1
  have hnA : ‖yi * diagonal z * yiᴴ‖ ≤ √B := norm_le_sqrt hA
  have hnN : ‖yᴴ * diagonal z * y‖ ≤ √B := by
    refine norm_le_sqrt ?_
    have e : yᴴ * diagonal z * y = (yᴴ * (diagonal z)ᴴ * y)ᴴ := by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, mul_assoc]
    rw [e, fr_conjTranspose]
    exact hN
  have hDD : diagonal z * diagonal z = diagonal w := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext b
    simp [w, sq]
  have hg : (yi * diagonal z * yiᴴ) * (yᴴ * diagonal z * y) = yi * diagonal w * y := by
    simp only [mul_assoc, c7]
    rw [← mul_assoc (diagonal z) (diagonal z) y, hDD]
  have hng : ‖yi * diagonal w * y‖ ≤ B := by
    rw [← hg]
    calc ‖(yi * diagonal z * yiᴴ) * (yᴴ * diagonal z * y)‖
        ≤ ‖yi * diagonal z * yiᴴ‖ * ‖yᴴ * diagonal z * y‖ := norm_mul_le _ _
      _ ≤ √B * √B := mul_le_mul hnA hnN (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = B := Real.mul_self_sqrt hB
  have hP : ∀ a, ‖yi * diagonal (fun b => if b = a then (1 : ℂ) else 0) * y‖ ≤ K a := by
    intro a
    have e := poly_conj h1 h2 (L a) w
    have hev : (fun b => (L a).eval (w b)) = fun b => if b = a then (1 : ℂ) else 0 := by
      funext b
      by_cases hb : b = a
      · subst hb
        rw [if_pos rfl]
        exact Lagrange.eval_basis_self hinjw (Finset.mem_univ _)
      · rw [if_neg hb]
        exact Lagrange.eval_basis_of_ne (Ne.symm hb) (Finset.mem_univ _)
    rw [hev] at e
    rw [← e]
    exact norm_poly_bound (L a) hng
  have hf1 : ∀ a, (fun b => (if b = a then (1 : ℂ) else 0) * z b) = fun b => if b = a then z a else 0 := by
    intro a
    funext b
    by_cases hb : b = a
    · subst hb; simp
    · simp [hb]
  have hf2 : ∀ a, (fun b => z b * (if b = a then (1 : ℂ) else 0)) = fun b => if b = a then z a else 0 := by
    intro a
    funext b
    by_cases hb : b = a
    · subst hb; simp
    · simp [hb]
  have hyi : ∀ i a, ‖yi i a‖ ^ 2 ≤ K a * √B := by
    intro i a
    have e : (yi * diagonal (fun b => if b = a then (1 : ℂ) else 0) * y) * (yi * diagonal z * yiᴴ)
        = yi * diagonal (fun b => if b = a then z a else 0) * yiᴴ := by
      simp only [mul_assoc, c3]
      rw [← mul_assoc (diagonal _) (diagonal z) yiᴴ, diagonal_mul_diagonal, hf1 a]
    have h := entry_le (yi * diagonal (fun b => if b = a then z a else 0) * yiᴴ) i i
    rw [entry_single, norm_mul, hz a, one_mul, Complex.norm_of_nonneg (sq_nonneg _), ← e] at h
    exact h.trans ((norm_mul_le _ _).trans
      (mul_le_mul (hP a) hnA (norm_nonneg _) ((norm_nonneg _).trans (hP a))))
  have hyy : ∀ a i, ‖y a i‖ ^ 2 ≤ √B * K a := by
    intro a i
    have e : (yᴴ * diagonal z * y) * (yi * diagonal (fun b => if b = a then (1 : ℂ) else 0) * y)
        = yᴴ * diagonal (fun b => if b = a then z a else 0) * yᴴᴴ := by
      rw [conjTranspose_conjTranspose]
      simp only [mul_assoc, c3]
      rw [← mul_assoc (diagonal z) (diagonal _) y, diagonal_mul_diagonal, hf2 a]
    have h := entry_le (yᴴ * diagonal (fun b => if b = a then z a else 0) * yᴴᴴ) i i
    rw [entry_single, norm_mul, hz a, one_mul, Complex.norm_of_nonneg (sq_nonneg _), ← e,
      conjTranspose_apply, norm_star] at h
    exact h.trans ((norm_mul_le _ _).trans
      (mul_le_mul hnN (hP a) (norm_nonneg _) (Real.sqrt_nonneg _)))
  constructor
  · calc fr y = ∑ a, ∑ i, ‖y a i‖ ^ 2 := rfl
      _ ≤ ∑ a, ∑ i : Fin n, √B * K a :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun i _ => hyy a i
      _ = n * ∑ a, K a * √B := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => by ring
  · calc fr yi = ∑ i, ∑ a, ‖yi i a‖ ^ 2 := rfl
      _ ≤ ∑ i : Fin n, ∑ a, K a * √B :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ => hyi i a
      _ = n * ∑ a, K a * √B := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Frobenius

theorem cone_step {P Q c : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef) {s M K₀ T' : ℝ}
    (hT : (T' • P - 1).PosSemidef) (hc : c = s • P + (1 - s) • (1 : Matrix (Fin n) (Fin n) ℂ))
    (h1 : (M • Q - c).PosSemidef) (h2 : (M • c - Q).PosSemidef) (h3 : (1 - s) * T' ≤ K₀)
    (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1) (hM : 1 ≤ M) (hK : 0 ≤ K₀) :
    ((M * (2 + K₀)) • Q - P).PosSemidef ∧ ((M * (2 + K₀)) • P - Q).PosSemidef := by
  subst hc
  constructor
  · have hA := (((psd_rsmul h1 (t := 2) (by norm_num)).add
      (psd_rsmul (psd_rsmul Matrix.PosSemidef.one (t := 1 - s) (by linarith)) (t := 2) (by norm_num))).add
      (psd_rsmul hP (t := 2 * s - 1) (by linarith))).add (psd_rsmul hQ (t := M * K₀) (by positivity))
    convert hA using 1
    module
  · have hB := (((h2.add (psd_rsmul hT (t := M * (1 - s)) (mul_nonneg (by linarith) (by linarith)))).add
      (psd_rsmul hP (t := M * (K₀ - (1 - s) * T')) (mul_nonneg (by linarith) (by linarith)))).add
      (psd_rsmul hP (t := M * (2 - s)) (mul_nonneg (by linarith) (by linarith))))
    convert hB using 1
    module

def bnd (M : ℝ) (n : ℕ) : ℝ := M * (2 * M * n + n + 1) + 2 * M * n + 1

def cmp (M : ℝ) (n : ℕ) : ℝ := M * (2 + M ^ 2 * (n : ℝ) ^ 2)

theorem trace_conj_unitary {d : Matrix (Fin n) (Fin n) ℂ} (hd : dᴴ * d = 1) (u : Matrix (Fin n) (Fin n) ℂ) :
    ((d * u) * (d * u)ᴴ).trace = (fr u : ℂ) := by
  calc ((d * u) * (d * u)ᴴ).trace = (d * (u * uᴴ * dᴴ)).trace := by
        rw [conjTranspose_mul]; simp only [mul_assoc]
    _ = (u * uᴴ * dᴴ * d).trace := by rw [trace_mul_comm]
    _ = (u * uᴴ).trace := by rw [mul_assoc (u * uᴴ), hd, mul_one]
    _ = (fr u : ℂ) := trace_mul_conjTranspose u

private theorem psd_le_lemma_2 {N : Matrix (Fin n) (Fin n) ℂ} {M : ℝ} (hM : fr N ≤ M) :
    (M • (1 : Matrix (Fin n) (Fin n) ℂ) - N * Nᴴ).PosSemidef := by
  have e : (M • (1 : Matrix (Fin n) (Fin n) ℂ)) - N * Nᴴ =
      (M - fr N) • (1 : Matrix (Fin n) (Fin n) ℂ) + (fr N • (1 : Matrix (Fin n) (Fin n) ℂ) - N * Nᴴ) := by
    rw [sub_smul]; abel
  rw [e]
  exact (psd_rsmul Matrix.PosSemidef.one (sub_nonneg.2 hM)).add (psd_fr N)

private theorem tr_push_algHom_eq_map_tr {X : Matrix (Fin n) (Fin n) ℂ} {t : ℝ}
    (h : (t • (1 : Matrix (Fin n) (Fin n) ℂ) - X * Xᴴ).PosSemidef) : fr X ≤ t * n := by
  have h1 := psd_trace h
  rw [trace_mul_conjTranspose, Complex.ofReal_re] at h1
  have h2 : ((t • (1 : Matrix (Fin n) (Fin n) ℂ)).trace).re = t * n := by
    rw [trace_smul, trace_one, Fintype.card_fin, Complex.smul_re, smul_eq_mul, Complex.natCast_re]
  linarith

theorem contraction_dichotomy (hn : 0 < n) {x xi y yi d : Matrix (Fin n) (Fin n) ℂ} (hx1 : x * xi = 1) (hx2 : xi * x = 1)
    (hy1 : y * yi = 1) (hy2 : yi * y = 1) (hd1 : d * dᴴ = 1) (hd2 : dᴴ * d = 1) {s M : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hM : 1 ≤ M) (hc : x * xᴴ = s • (y * yᴴ) + (1 - s) • (1 : Matrix (Fin n) (Fin n) ℂ))
    (hA : fr (xi * d * yiᴴ) ≤ M) (hN : fr (yᴴ * dᴴ * x) ≤ M) :
    (fr y ≤ bnd M n ∧ fr yi ≤ bnd M n) ∨ (fr (yi * d * yiᴴ) ≤ n * cmp M n ∧ fr (yᴴ * dᴴ * y) ≤ n * cmp M n) := by
  have c1 := cancel_lemma hx1
  have c3 := cancel_lemma hy1
  have c4 := cancel_lemma hy2
  have c5 := cancel_lemma hd1
  have c6 := cancel_lemma hd2
  have hy1' : yiᴴ * yᴴ = 1 := by rw [← conjTranspose_mul, hy1, conjTranspose_one]
  have hy2' : yᴴ * yiᴴ = 1 := by rw [← conjTranspose_mul, hy2, conjTranspose_one]
  have hx1' : xiᴴ * xᴴ = 1 := by rw [← conjTranspose_mul, hx1, conjTranspose_one]
  have c7 := cancel_lemma hy1'
  have c8 := cancel_lemma hy2'
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hfry := fr_nonneg y
  have hfryi := fr_nonneg yi
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have G1 : (1 - s) * fr y ≤ M := by
    have e : (yᴴ * dᴴ * x) * (yᴴ * dᴴ * x)ᴴ =
        s • ((yᴴ * dᴴ * y) * (yᴴ * dᴴ * y)ᴴ) + (1 - s) • (yᴴ * yᴴᴴ) := by
      have e0 : (yᴴ * dᴴ * x) * (yᴴ * dᴴ * x)ᴴ = yᴴ * dᴴ * (x * xᴴ) * d * y := by
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, mul_assoc]
      rw [e0, hc]
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, mul_assoc, c6]
    have t := congrArg Matrix.trace e
    rw [trace_mul_conjTranspose, trace_add, trace_smul, trace_smul, trace_mul_conjTranspose,
      trace_mul_conjTranspose, fr_conjTranspose] at t
    have t' := congrArg Complex.re t
    simp only [Complex.ofReal_re, Complex.add_re, Complex.smul_re, smul_eq_mul] at t'
    nlinarith [mul_nonneg hs0 (fr_nonneg (yᴴ * dᴴ * y))]
  have G2 : fr yi ≤ M * (s * fr y + (1 - s) * n) := by
    have hdd : dᴴᴴ * dᴴ = 1 := by rw [conjTranspose_conjTranspose]; exact hd1
    have e1 : dᴴ * (x * (xi * d * yiᴴ)) = yiᴴ := by simp only [mul_assoc, c1, c6]
    have e2 : fr yi = fr (x * (xi * d * yiᴴ)) := by
      have h := trace_conj_unitary hdd (x * (xi * d * yiᴴ))
      rw [e1, trace_mul_conjTranspose, fr_conjTranspose] at h
      exact_mod_cast h
    have h3 := psd_trace (psd_sandwich (W := x) hA)
    rw [trace_mul_conjTranspose, Complex.ofReal_re, hc] at h3
    have h4 : ((M • (s • (y * yᴴ) + (1 - s) • (1 : Matrix (Fin n) (Fin n) ℂ))).trace).re =
        M * (s * fr y + (1 - s) * n) := by
      rw [trace_smul, trace_add, trace_smul, trace_smul, trace_mul_conjTranspose, trace_one, Fintype.card_fin]
      simp only [Complex.smul_re, Complex.add_re, Complex.ofReal_re, Complex.natCast_re, smul_eq_mul]
    rw [e2]
    linarith
  by_cases hcase : 1 ≤ 2 * n * (1 - s)
  · left
    have hy : fr y ≤ 2 * M * n := by
      nlinarith [mul_le_mul_of_nonneg_left hcase hfry,
        mul_le_mul_of_nonneg_left G1 (by positivity : (0 : ℝ) ≤ 2 * n)]
    have hyi : fr yi ≤ M * (2 * M * n + n + 1) := by
      have a1 : s * fr y ≤ fr y := by nlinarith
      have a2 : (1 - s) * n ≤ n := by nlinarith
      have a3 : M * (s * fr y + (1 - s) * n) ≤ M * (2 * M * n + n + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hM0
      linarith
    have hMn : 0 ≤ M * n := mul_nonneg hM0 (by positivity)
    have hb1 : 0 ≤ M * (2 * M * n + n + 1) := mul_nonneg hM0 (by nlinarith)
    unfold bnd
    constructor <;> nlinarith
  · right
    rw [not_le] at hcase
    have hs : 1 / 2 ≤ s := by nlinarith [mul_le_mul_of_nonneg_right hn1 (sub_nonneg.2 hs1)]
    have hQ : (d * (yiᴴ * yi) * dᴴ).PosSemidef :=
      (posSemidef_conjTranspose_mul_self yi).mul_mul_conjTranspose_same d
    have hT : (fr yi • (y * yᴴ) - 1).PosSemidef := by
      have h := psd_conj (psd_fr yi) y
      convert h using 1
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, mul_assoc, c3, hy1']
    have h1 : (M • (d * (yiᴴ * yi) * dᴴ) - x * xᴴ).PosSemidef := by
      have h := psd_conj (psd_le_lemma_2 hN) (d * yiᴴ)
      convert h using 1
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, Matrix.one_mul, mul_assoc, c3, c5, c7, hd1]
    have h2 : (M • (x * xᴴ) - d * (yiᴴ * yi) * dᴴ).PosSemidef := by
      have h := psd_conj (psd_le_lemma_2 hA) x
      convert h using 1
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, Matrix.one_mul, mul_assoc, c1, hx1']
    have h3 : (1 - s) * fr yi ≤ M ^ 2 * (n : ℝ) ^ 2 := by
      have a1 : (1 - s) * fr yi ≤ (1 - s) * (M * (s * fr y + (1 - s) * n)) :=
        mul_le_mul_of_nonneg_left G2 (by linarith)
      have a3 : M * s * ((1 - s) * fr y) ≤ M * s * M := mul_le_mul_of_nonneg_left G1 (mul_nonneg hM0 hs0)
      have a4 : (1 - s) * (1 - s) ≤ (1 - s) * M := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have a5 : M * ((1 - s) * (1 - s)) * n ≤ M * ((1 - s) * M) * n :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left a4 hM0) (by positivity)
      have b1 : 0 ≤ M ^ 2 * s * (n - 1) := mul_nonneg (mul_nonneg (sq_nonneg M) hs0) (by linarith)
      have b2 : M ^ 2 * n ≤ M ^ 2 * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg M)
      nlinarith [a1, a3, a5, b1, b2]
    obtain ⟨hq1, hq2⟩ := cone_step (posSemidef_self_mul_conjTranspose y) hQ hT hc h1 h2 h3 hs hs1 hM
      (by positivity)
    constructor
    · have h := psd_conj hq2 yi
      have e : yi * ((M * (2 + M ^ 2 * (n : ℝ) ^ 2)) • (y * yᴴ)) * yiᴴ - yi * (d * (yiᴴ * yi) * dᴴ) * yiᴴ =
          (M * (2 + M ^ 2 * (n : ℝ) ^ 2)) • (1 : Matrix (Fin n) (Fin n) ℂ) - (yi * d * yiᴴ) * (yi * d * yiᴴ)ᴴ := by
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul,
          mul_assoc, c4, hy2']
      rw [e] at h
      have := tr_push_algHom_eq_map_tr h
      unfold cmp
      linarith
    · have h := psd_conj hq1 (yᴴ * dᴴ)
      have e : yᴴ * dᴴ * ((M * (2 + M ^ 2 * (n : ℝ) ^ 2)) • (d * (yiᴴ * yi) * dᴴ)) * (yᴴ * dᴴ)ᴴ -
          yᴴ * dᴴ * (y * yᴴ) * (yᴴ * dᴴ)ᴴ =
          (M * (2 + M ^ 2 * (n : ℝ) ^ 2)) • (1 : Matrix (Fin n) (Fin n) ℂ) - (yᴴ * dᴴ * y) * (yᴴ * dᴴ * y)ᴴ := by
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one, mul_assoc, c6, c8, hy2, hy2']
      rw [e] at h
      have := tr_push_algHom_eq_map_tr h
      unfold cmp
      linarith

theorem lg_eq (y : Matrix (Fin n) (Fin n) ℂ) : PositivityTheory.RgBcC.lg y = Real.log (1 + (fr y + fr y⁻¹)) := by
  unfold PositivityTheory.RgBcC.lg fr
  congr 2
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_add_distrib]

theorem real_coe_smul (r : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) : (r : ℂ) • A = r • A := by
  ext i j
  simp [Complex.real_smul]

theorem suppSt : PositivityTheory.RgBcC.SuppSt := by
  intro n z hz hinj R
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = max (Real.exp R) 1 := ⟨_, rfl⟩
  have hM : 1 ≤ M := by rw [hMdef]; exact le_max_right _ _
  have hME : Real.exp R ≤ M := by rw [hMdef]; exact le_max_left _ _
  obtain ⟨C, hC⟩ := bounded_of_conj z hz hinj (n * cmp M n)
  refine ⟨Real.log (1 + 2 * max (bnd M n) C), ?_⟩
  intro s hs x hx y hy hc hlg
  obtain ⟨hs0, hs1⟩ := hs
  have hxd : Matrix.det (x : Matrix (Fin n) (Fin n) ℂ) ≠ 0 := hx
  have hyd : Matrix.det (y : Matrix (Fin n) (Fin n) ℂ) ≠ 0 := hy
  have hxu : IsUnit (Matrix.det (x : Matrix (Fin n) (Fin n) ℂ)) := isUnit_iff_ne_zero.2 hxd
  have hyu : IsUnit (Matrix.det (y : Matrix (Fin n) (Fin n) ℂ)) := isUnit_iff_ne_zero.2 hyd
  have hx1 : x * x⁻¹ = 1 := Matrix.mul_nonsing_inv x hxu
  have hx2 : x⁻¹ * x = 1 := Matrix.nonsing_inv_mul x hxu
  have hy1 : y * y⁻¹ = 1 := Matrix.mul_nonsing_inv y hyu
  have hy2 : y⁻¹ * y = 1 := Matrix.nonsing_inv_mul y hyu
  have hdd1 : diagonal z * (diagonal z)ᴴ = 1 := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    simp only [Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz a]
    norm_num
  have hdd2 : (diagonal z)ᴴ * diagonal z = 1 := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', hz a]
    norm_num
  have hinvA : (x⁻¹ * diagonal z * (yᴴ)⁻¹)⁻¹ = yᴴ * (diagonal z)ᴴ * x := by
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.conjTranspose_nonsing_inv]
    simp only [mul_assoc]
    rw [← mul_assoc (y⁻¹ᴴ) yᴴ, ← conjTranspose_mul, hy1, conjTranspose_one, Matrix.one_mul,
      ← mul_assoc (diagonal z), hdd1, Matrix.one_mul, hx2]
  have hlg' := hlg
  rw [lg_eq, hinvA, ← Matrix.conjTranspose_nonsing_inv] at hlg'
  have hf1 := fr_nonneg (x⁻¹ * diagonal z * y⁻¹ᴴ)
  have hf2 := fr_nonneg (yᴴ * (diagonal z)ᴴ * x)
  rw [Real.log_le_iff_le_exp (by linarith)] at hlg'
  have hA : fr (x⁻¹ * diagonal z * y⁻¹ᴴ) ≤ M := by linarith
  have hN : fr (yᴴ * (diagonal z)ᴴ * x) ≤ M := by linarith
  have hc' : x * xᴴ = s • (y * yᴴ) + (1 - s) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [real_coe_smul, real_coe_smul] at hc
    exact hc
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hbnd0 : 0 ≤ bnd M n := by
    unfold bnd
    have : 0 ≤ M * (2 * M * n + n + 1) := mul_nonneg (by linarith) (by nlinarith)
    nlinarith
  have key : fr y ≤ max (bnd M n) C ∧ fr y⁻¹ ≤ max (bnd M n) C := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0 : ∀ A : Matrix (Fin 0) (Fin 0) ℂ, fr A = 0 := fun A => by simp [fr]
      rw [h0, h0]
      exact ⟨le_max_of_le_left hbnd0, le_max_of_le_left hbnd0⟩
    · rcases contraction_dichotomy hn hx1 hx2 hy1 hy2 hdd1 hdd2 hs0 hs1 hM hc' hA hN with h | h
      · exact ⟨le_max_of_le_left h.1, le_max_of_le_left h.2⟩
      · obtain ⟨h1, h2⟩ := hC y y⁻¹ hy1 hy2 h.1 h.2
        exact ⟨le_max_of_le_right h1, le_max_of_le_right h2⟩
  rw [lg_eq]
  apply Real.log_le_log (by linarith [fr_nonneg y, fr_nonneg y⁻¹])
  linarith [key.1, key.2]

end GlobalTheory.CompanionTheory.SuppBound
