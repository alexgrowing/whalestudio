import Formalism.SizeWindowBrackets.TraceSquareAndDiagBounds

open Matrix
open scoped ComplexOrder

namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare

noncomputable section

section HS

variable {m n k : Type} [Fintype m] [Fintype n] [Fintype k]

lemma hsSq_nonneg (M : Matrix m n ℂ) : 0 ≤ hsSq M := by
  unfold hsSq
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

private theorem star_mul_self_eq_norm_sq (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rfl

lemma trace_conjTranspose_mul_self (M : Matrix m n ℂ) :
    (Mᴴ * M).trace = ((hsSq M : ℝ) : ℂ) := by
  have h : (Mᴴ * M).trace = ∑ j, ∑ i, star (M i j) * M i j := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [h, Finset.sum_comm]
  simp only [star_mul_self_eq_norm_sq, hsSq, Complex.ofReal_sum]

lemma hsSq_eq_re (M : Matrix m n ℂ) : hsSq M = (Mᴴ * M).trace.re := by
  rw [trace_conjTranspose_mul_self, Complex.ofReal_re]

lemma hsSq_conjTranspose (M : Matrix m n ℂ) : hsSq Mᴴ = hsSq M := by
  simp only [hsSq, Matrix.conjTranspose_apply, norm_star]
  exact Finset.sum_comm

lemma hsSq_smul (c : ℂ) (M : Matrix m n ℂ) : hsSq (c • M) = ‖c‖ ^ 2 * hsSq M := by
  simp only [hsSq, Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

end HS

section Fam

variable {ι : Type} [Fintype ι] {D : ℕ} {d : ι → ℕ}

lemma Kd_eq (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u) (u : ι) :
    Kd B ga u = ((ga u : ℝ) : ℂ) • ((B u)ᴴ * B u) := by
  unfold Kd Kp
  rw [Real.sqrt_mul_self (hga u)]

lemma trace_Qm (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u) :
    (Qm B ga).trace = ∑ u, (Kd B ga u).trace := by
  unfold Qm
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Kd_eq B ga hga u, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_mul_comm]

lemma hsSq_Kp (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u)
    (u u' : ι) : hsSq (Kp B ga u u') = ga u * ga u' * hsSq ((B u)ᴴ * B u') := by
  unfold Kp
  rw [hsSq_smul]
  have hn : ‖((Real.sqrt (ga u * ga u') : ℝ) : ℂ)‖ ^ 2 = ga u * ga u' := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (mul_nonneg (hga u) (hga u'))]
  rw [hn]

lemma trace_Qm_sq (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u) :
    (Qm B ga * Qm B ga).trace = (((∑ u, ∑ u', hsSq (Kp B ga u u') : ℝ)) : ℂ) := by
  have key : ∀ u u', ((((ga u : ℝ) : ℂ) • (B u * (B u)ᴴ)) * (((ga u' : ℝ) : ℂ) • (B u' * (B u')ᴴ))).trace
      = ((hsSq (Kp B ga u u') : ℝ) : ℂ) := by
    intro u u'
    have h2 : (B u * (B u)ᴴ * (B u' * (B u')ᴴ)).trace
        = (((B u)ᴴ * B u')ᴴ * ((B u)ᴴ * B u')).trace := by
      rw [Matrix.trace_mul_comm ((B u)ᴴ * B u')ᴴ, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm (B u)]
      simp only [Matrix.mul_assoc]
    rw [hsSq_Kp B ga hga u u']
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    rw [h2, trace_conjTranspose_mul_self]
    simp only [Complex.ofReal_mul]
    ring
  unfold Qm
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => ?_
  rw [Matrix.trace_mul_comm]
  exact key u u'

end Fam

section CS

variable {m n : Type} [Fintype m] [Fintype n]

private theorem le_sqrt_of_sq_le' {x y : ℝ} (h : x ^ 2 ≤ y) : x ≤ Real.sqrt y := by
  refine (le_abs_self x).trans ?_
  exact Real.abs_le_sqrt h

private theorem sum_norm_mul_le_hsNorm_mul (A B : Matrix m n ℂ) :
    ∑ i, ∑ j, ‖A i j‖ * ‖B i j‖ ≤ hsNorm A * hsNorm B := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (m × n))
    (fun p => ‖A p.1 p.2‖) (fun p => ‖B p.1 p.2‖)
  simp only [Fintype.sum_prod_type] at h
  unfold hsNorm
  rw [← Real.sqrt_mul (hsSq_nonneg A)]
  exact le_sqrt_of_sq_le' h

lemma norm_trace_mul_le (X : Matrix m n ℂ) (Y : Matrix n m ℂ) :
    ‖(X * Y).trace‖ ≤ hsNorm X * hsNorm Y := by
  have h1 : ‖(X * Y).trace‖ ≤ ∑ i, ∑ j, ‖X i j‖ * ‖Yᵀ i j‖ := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
  have h2 : hsNorm Yᵀ = hsNorm Y := by
    unfold hsNorm hsSq
    simp only [Matrix.transpose_apply]
    rw [Finset.sum_comm]
  rw [← h2]
  exact h1.trans (sum_norm_mul_le_hsNorm_mul X Yᵀ)

lemma hsSq_one (n : ℕ) : hsSq (1 : Matrix (Fin n) (Fin n) ℂ) = n := by
  have h : ∀ i j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  unfold hsSq
  simp [h]

end CS

private theorem re_le_norm' (z : ℂ) : z.re ≤ ‖z‖ := by
  exact Complex.re_le_norm z

private theorem neg_re_le_norm' (z : ℂ) : -z.re ≤ ‖z‖ := by
  have h := re_le_norm' (-z)
  rwa [Complex.neg_re, norm_neg] at h

theorem traceLowerBound : TraceLower := by
  intro n K
  have h1 : K.trace = (n : ℂ) + ((1 : Matrix (Fin n) (Fin n) ℂ) * (K - 1)).trace := by
    rw [one_mul, Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin]
    ring
  have h2 := norm_trace_mul_le (1 : Matrix (Fin n) (Fin n) ℂ) (K - 1)
  have h3 : hsNorm (1 : Matrix (Fin n) (Fin n) ℂ) = Real.sqrt n := by
    unfold hsNorm
    rw [hsSq_one]
  rw [h3] at h2
  have h4 := neg_re_le_norm' (((1 : Matrix (Fin n) (Fin n) ℂ) * (K - 1)).trace)
  have h5 : ((n : ℂ)).re = (n : ℝ) := by simp
  rw [h1, Complex.add_re, h5]
  linarith

section Tri

variable {m n : Type} [Fintype m] [Fintype n]

lemma hsNorm_nonneg (M : Matrix m n ℂ) : 0 ≤ hsNorm M :=
  Real.sqrt_nonneg _

lemma hsNorm_sq (M : Matrix m n ℂ) : hsNorm M ^ 2 = hsSq M :=
  Real.sq_sqrt (hsSq_nonneg M)

lemma hsSq_add_le (A B : Matrix m n ℂ) : hsSq (A + B) ≤ (hsNorm A + hsNorm B) ^ 2 := by
  have h1 : hsSq (A + B)
      ≤ ∑ i, ∑ j, (‖A i j‖ ^ 2 + ‖B i j‖ ^ 2 + 2 * (‖A i j‖ * ‖B i j‖)) := by
    unfold hsSq
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    rw [Matrix.add_apply]
    nlinarith [norm_add_le (A i j) (B i j), norm_nonneg (A i j + B i j), norm_nonneg (A i j),
      norm_nonneg (B i j)]
  have e : ∑ i, ∑ j, (‖A i j‖ ^ 2 + ‖B i j‖ ^ 2 + 2 * (‖A i j‖ * ‖B i j‖))
      = hsSq A + hsSq B + 2 * ∑ i, ∑ j, ‖A i j‖ * ‖B i j‖ := by
    unfold hsSq
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have h2 := sum_norm_mul_le_hsNorm_mul A B
  have hA := hsNorm_sq A
  have hB := hsNorm_sq B
  nlinarith [hsNorm_nonneg A, hsNorm_nonneg B]

lemma hsNorm_le_of_sq (M : Matrix m n ℂ) {e x : ℝ} (he : 0 ≤ e) (h : hsSq M ≤ e * x) :
    hsNorm M ≤ Real.sqrt e * Real.sqrt x := by
  unfold hsNorm
  rw [← Real.sqrt_mul he]
  exact Real.sqrt_le_sqrt h

end Tri

lemma hsSq_le_of_sub_one (n : ℕ) (K : Matrix (Fin n) (Fin n) ℂ) :
    hsSq K ≤ (Real.sqrt n + hsNorm (K - 1)) ^ 2 := by
  have h := hsSq_add_le (1 : Matrix (Fin n) (Fin n) ℂ) (K - 1)
  rw [show (1 : Matrix (Fin n) (Fin n) ℂ) + (K - 1) = K by abel] at h
  have h1 : hsNorm (1 : Matrix (Fin n) (Fin n) ℂ) = Real.sqrt n := by
    unfold hsNorm
    rw [hsSq_one]
  rwa [h1] at h

section Cor

variable {ι : Type} [Fintype ι] {D : ℕ} {d : ι → ℕ}

lemma Rs_nonneg (d : ι → ℕ) : 0 ≤ Rs d := by
  unfold Rs
  exact Finset.sum_nonneg fun u _ => Nat.cast_nonneg _

lemma trQ_lower (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u)
    {e0 : ℝ} (he : 0 ≤ e0) (hK : ∀ u, hsSq (Kd B ga u - 1) ≤ e0 * (d u : ℝ)) :
    (1 - Real.sqrt e0) * Rs d ≤ (Qm B ga).trace.re := by
  have hu : ∀ u, (1 - Real.sqrt e0) * (d u : ℝ) ≤ (Kd B ga u).trace.re := by
    intro u
    have h1 := traceLowerBound (d u) (Kd B ga u)
    have h2 := hsNorm_le_of_sq _ he (hK u)
    have h3 : Real.sqrt (d u : ℝ) * Real.sqrt (d u : ℝ) = d u := Real.mul_self_sqrt (Nat.cast_nonneg _)
    have h4 := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg (d u : ℝ))
    have h5 : Real.sqrt (d u : ℝ) * (Real.sqrt e0 * Real.sqrt (d u : ℝ)) = Real.sqrt e0 * d u := by
      rw [show Real.sqrt (d u : ℝ) * (Real.sqrt e0 * Real.sqrt (d u : ℝ))
          = Real.sqrt e0 * (Real.sqrt (d u : ℝ) * Real.sqrt (d u : ℝ)) by ring, h3]
    linarith
  rw [trace_Qm B ga hga, Complex.re_sum]
  unfold Rs
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun u _ => hu u

lemma trQsq_upper (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u)
    {Dstar η0 e0 : ℝ} (hD : 0 < Dstar) (hη : -1 ≤ η0) (he : 0 ≤ e0)
    (hP : ∀ u u', u ≠ u' → hsSq (Kp B ga u u') ≤ (1 + η0) * (d u : ℝ) * (d u' : ℝ) / Dstar)
    (hK : ∀ u, hsSq (Kd B ga u - 1) ≤ e0 * (d u : ℝ)) :
    (Qm B ga * Qm B ga).trace.re ≤ (1 + η0) * Rs d ^ 2 / Dstar + (1 + Real.sqrt e0) ^ 2 * Rs d := by
  classical
  have hη' : 0 ≤ 1 + η0 := by linarith
  have hdiag : ∀ u, hsSq (Kp B ga u u) ≤ (1 + Real.sqrt e0) ^ 2 * (d u : ℝ) := by
    intro u
    have h1 := hsSq_le_of_sub_one (d u) (Kd B ga u)
    have h2 := hsNorm_le_of_sq _ he (hK u)
    have hx := hsNorm_nonneg (Kd B ga u - 1)
    have hy := Real.sqrt_nonneg (d u : ℝ)
    have h3 : Real.sqrt (d u : ℝ) + hsNorm (Kd B ga u - 1)
        ≤ (1 + Real.sqrt e0) * Real.sqrt (d u : ℝ) := by linarith
    have h4 : 0 ≤ Real.sqrt (d u : ℝ) + hsNorm (Kd B ga u - 1) := by linarith
    have h5 : (Real.sqrt (d u : ℝ) + hsNorm (Kd B ga u - 1)) ^ 2
        ≤ ((1 + Real.sqrt e0) * Real.sqrt (d u : ℝ)) ^ 2 := by
      first
      | exact pow_le_pow_left₀ h4 h3 2
      | exact pow_le_pow_left h4 h3 2
      | nlinarith
    have h6 : ((1 + Real.sqrt e0) * Real.sqrt (d u : ℝ)) ^ 2 = (1 + Real.sqrt e0) ^ 2 * (d u : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    show hsSq (Kd B ga u) ≤ _
    linarith
  have hterm : ∀ u u', hsSq (Kp B ga u u')
      ≤ (1 + η0) * (d u : ℝ) * (d u' : ℝ) / Dstar
        + (if u = u' then (1 + Real.sqrt e0) ^ 2 * (d u : ℝ) else 0) := by
    intro u u'
    by_cases h : u = u'
    · rw [if_pos h]
      rw [← h]
      have h0 : 0 ≤ (1 + η0) * (d u : ℝ) * (d u : ℝ) / Dstar :=
        div_nonneg (mul_nonneg (mul_nonneg hη' (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) hD.le
      have := hdiag u
      linarith
    · rw [if_neg h, add_zero]
      exact hP u u' h
  have e1 : ∑ u, ∑ u', (1 + η0) * (d u : ℝ) * (d u' : ℝ) / Dstar = (1 + η0) * Rs d ^ 2 / Dstar := by
    unfold Rs
    simp only [sq, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => ?_
    ring
  have e2 : ∑ u, ∑ u', (if u = u' then (1 + Real.sqrt e0) ^ 2 * (d u : ℝ) else 0)
      = (1 + Real.sqrt e0) ^ 2 * Rs d := by
    unfold Rs
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    first
    | (rw [Finset.sum_ite_eq]; simp)
    | simp
  rw [trace_Qm_sq B ga hga, Complex.ofReal_re]
  calc ∑ u, ∑ u', hsSq (Kp B ga u u')
      ≤ ∑ u, ∑ u', ((1 + η0) * (d u : ℝ) * (d u' : ℝ) / Dstar
        + (if u = u' then (1 + Real.sqrt e0) ^ 2 * (d u : ℝ) else 0)) :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun u' _ => hterm u u'
    _ = (1 + η0) * Rs d ^ 2 / Dstar + (1 + Real.sqrt e0) ^ 2 * Rs d := by
        simp only [Finset.sum_add_distrib]
        rw [e1, e2]

end Cor

section Compress

variable {m n k : Type} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq k]

lemma proj_herm (V : Matrix m k ℂ) : (1 - V * Vᴴ)ᴴ = 1 - V * Vᴴ := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

lemma proj_idem (V : Matrix m k ℂ) (hV : Vᴴ * V = 1) :
    (1 - V * Vᴴ) * (1 - V * Vᴴ) = 1 - V * Vᴴ := by
  have hP : V * Vᴴ * (V * Vᴴ) = V * Vᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul]
  simp only [sub_mul, mul_sub, one_mul, mul_one, hP]
  abel

lemma hsSq_split (V : Matrix m k ℂ) (hV : Vᴴ * V = 1) (M : Matrix m n ℂ) :
    hsSq M = hsSq (Vᴴ * M) + hsSq ((1 - V * Vᴴ) * M) := by
  have e1 : ((Vᴴ * M)ᴴ * (Vᴴ * M)).trace = (Mᴴ * (V * Vᴴ) * M).trace := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  have e2 : (((1 - V * Vᴴ) * M)ᴴ * ((1 - V * Vᴴ) * M)).trace
      = (Mᴴ * M).trace - (Mᴴ * (V * Vᴴ) * M).trace := by
    rw [Matrix.conjTranspose_mul, proj_herm V]
    rw [show Mᴴ * (1 - V * Vᴴ) * ((1 - V * Vᴴ) * M) = Mᴴ * ((1 - V * Vᴴ) * (1 - V * Vᴴ)) * M by
      simp only [Matrix.mul_assoc]]
    rw [proj_idem V hV, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.trace_sub]
  rw [hsSq_eq_re M, hsSq_eq_re (Vᴴ * M),
    hsSq_eq_re ((1 - V * Vᴴ) * M), e1, e2, Complex.sub_re]
  ring

lemma hsSq_left_le (V : Matrix m k ℂ) (hV : Vᴴ * V = 1) (M : Matrix m n ℂ) :
    hsSq (Vᴴ * M) ≤ hsSq M := by
  have h1 := hsSq_split V hV M
  have h2 := hsSq_nonneg ((1 - V * Vᴴ) * M)
  linarith

end Compress

lemma hsSq_compress {a b c e : ℕ} (V : Matrix (Fin a) (Fin c) ℂ) (hV : Vᴴ * V = 1)
    (W : Matrix (Fin b) (Fin e) ℂ) (hW : Wᴴ * W = 1) (M : Matrix (Fin a) (Fin b) ℂ) :
    hsSq (Vᴴ * M * W) ≤ hsSq M := by
  have h1 := hsSq_left_le W hW (Vᴴ * M)ᴴ
  have h2 := hsSq_left_le V hV M
  rw [← Matrix.conjTranspose_mul, hsSq_conjTranspose, hsSq_conjTranspose] at h1
  linarith

section Ram

variable {ι : Type} [Fintype ι] {D : ℕ} {d r : ι → ℕ}

lemma Kp_ram (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ)
    (ga : ι → ℝ) (u u' : ι) : Kp (Bram B V) ga u u' = (V u)ᴴ * Kp B ga u u' * V u' := by
  simp only [Kp, Bram, Matrix.conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_assoc]

lemma Kd_ram_sub (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ)
    (ga : ι → ℝ) (hV : Isom V) (u : ι) :
    Kd (Bram B V) ga u - 1 = (V u)ᴴ * (Kd B ga u - 1) * V u := by
  have hV' : ∀ u, (V u)ᴴ * V u = 1 := hV
  have h := Kp_ram B V ga u u
  unfold Kd
  rw [h, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV' u]

end Ram

section RamTr

lemma trace_proj (n k : ℕ) (V : Matrix (Fin n) (Fin k) ℂ) (hV : Vᴴ * V = 1) :
    (1 - V * Vᴴ).trace = ((((n : ℝ) - (k : ℝ)) : ℝ) : ℂ) := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, hV, Matrix.trace_one, Matrix.trace_one,
    Fintype.card_fin, Fintype.card_fin]
  push_cast
  ring

lemma ram_gap (n k : ℕ) (K : Matrix (Fin n) (Fin n) ℂ) (V : Matrix (Fin n) (Fin k) ℂ)
    (hV : Vᴴ * V = 1) {e0 : ℝ} (he : 0 ≤ e0) (hK : hsSq (K - 1) ≤ e0 * n) :
    0 ≤ (n : ℝ) - k ∧
    K.trace.re - (Vᴴ * K * V).trace.re
      ≤ ((n : ℝ) - k) + Real.sqrt ((n : ℝ) - k) * (Real.sqrt e0 * Real.sqrt n) := by
  have hP1 : (1 - V * Vᴴ)ᴴ * (1 - V * Vᴴ) = 1 - V * Vᴴ := by
    rw [proj_herm V, proj_idem V hV]
  have hnk : hsSq (1 - V * Vᴴ) = (n : ℝ) - k := by
    have h := trace_conjTranspose_mul_self (1 - V * Vᴴ)
    rw [hP1, trace_proj n k V hV] at h
    exact (Complex.ofReal_injective h).symm
  have hnk0 : 0 ≤ (n : ℝ) - k := by
    rw [← hnk]
    exact hsSq_nonneg _
  refine ⟨hnk0, ?_⟩
  have hc : (Vᴴ * K * V).trace = (K * (V * Vᴴ)).trace := by
    rw [Matrix.trace_mul_comm (Vᴴ * K) V, Matrix.trace_mul_comm K (V * Vᴴ), Matrix.mul_assoc]
  have htr : K.trace - (Vᴴ * K * V).trace
      = (1 - V * Vᴴ).trace + ((K - 1) * (1 - V * Vᴴ)).trace := by
    rw [hc]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.trace_sub]
    ring
  have hcs := norm_trace_mul_le (K - 1) (1 - V * Vᴴ)
  have hN1 : hsNorm (1 - V * Vᴴ) = Real.sqrt ((n : ℝ) - k) := by
    unfold hsNorm
    rw [hnk]
  rw [hN1] at hcs
  have hNK := hsNorm_le_of_sq _ he hK
  have hre : (K.trace - (Vᴴ * K * V).trace).re
      = ((n : ℝ) - k) + ((K - 1) * (1 - V * Vᴴ)).trace.re := by
    rw [htr, Complex.add_re, trace_proj n k V hV, Complex.ofReal_re]
  rw [Complex.sub_re] at hre
  have habs := re_le_norm' (((K - 1) * (1 - V * Vᴴ)).trace)
  have hs := Real.sqrt_nonneg ((n : ℝ) - k)
  have hm := mul_le_mul_of_nonneg_left hNK hs
  linarith

end RamTr

section RamMain

variable {ι : Type} [Fintype ι] {D : ℕ} {d r : ι → ℕ}

private theorem sum_sqrt_mul_sqrt_le_sqrt_sum_mul' {κ : Type} [Fintype κ] (a b : κ → ℝ) (ha : ∀ u, 0 ≤ a u)
    (hb : ∀ u, 0 ≤ b u) :
    ∑ u, Real.sqrt (a u) * Real.sqrt (b u) ≤ Real.sqrt (∑ u, a u) * Real.sqrt (∑ u, b u) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun u => Real.sqrt (a u))
    (fun u => Real.sqrt (b u))
  have ea : ∀ u, Real.sqrt (a u) ^ 2 = a u := fun u => Real.sq_sqrt (ha u)
  have eb : ∀ u, Real.sqrt (b u) ^ 2 = b u := fun u => Real.sq_sqrt (hb u)
  simp only [ea, eb] at h
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun u _ => ha u)]
  exact le_sqrt_of_sq_le' h

theorem compressTraceLowerBound : RamTrace := by
  intro ι _ D d r B V ga de e0 hV hga hde he hK hsum
  have hV' : ∀ u, (V u)ᴴ * V u = 1 := hV
  have hu : ∀ u, (Kd B ga u).trace.re - (Kd (Bram B V) ga u).trace.re
      ≤ ((d u : ℝ) - r u) + Real.sqrt ((d u : ℝ) - r u) * (Real.sqrt e0 * Real.sqrt (d u)) := by
    intro u
    have e : Kd (Bram B V) ga u = (V u)ᴴ * Kd B ga u * V u :=
      Kp_ram B V ga u u
    rw [e]
    exact (ram_gap (d u) (r u) (Kd B ga u) (V u) (hV' u) he
      (hK u)).2
  have hnn : ∀ u, 0 ≤ (d u : ℝ) - r u := fun u =>
    (ram_gap (d u) (r u) (Kd B ga u) (V u) (hV' u) he (hK u)).1
  have hCS : ∑ u, Real.sqrt ((d u : ℝ) - r u) * Real.sqrt (d u)
      ≤ Real.sqrt (∑ u, ((d u : ℝ) - r u)) * Real.sqrt (Rs d) :=
    sum_sqrt_mul_sqrt_le_sqrt_sum_mul' _ _ hnn (fun u => Nat.cast_nonneg _)
  have h3 : Real.sqrt (∑ u, ((d u : ℝ) - r u)) ≤ Real.sqrt de * Real.sqrt (Rs d) := by
    rw [← Real.sqrt_mul hde]
    exact Real.sqrt_le_sqrt hsum
  have hT : Real.sqrt (Rs d) * Real.sqrt (Rs d) = Rs d :=
    Real.mul_self_sqrt (Rs_nonneg d)
  have h4 : ∑ u, Real.sqrt ((d u : ℝ) - r u) * Real.sqrt (d u) ≤ Real.sqrt de * Rs d := by
    have h := mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg (Rs d))
    rw [mul_assoc, hT] at h
    linarith
  have h5 := mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg e0)
  have h2 : ∑ u, Real.sqrt ((d u : ℝ) - r u) * (Real.sqrt e0 * Real.sqrt (d u))
      = Real.sqrt e0 * ∑ u, Real.sqrt ((d u : ℝ) - r u) * Real.sqrt (d u) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring
  have hsumu := Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) => hu u
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, h2] at hsumu
  rw [trace_Qm B ga hga, trace_Qm (Bram B V) ga hga, Complex.re_sum,
    Complex.re_sum, Real.sqrt_mul hde e0]
  linarith

theorem compressDiagDefectBound : CompressDiagDefectBound := by
  intro ι _ D d r B V ga de e0 hV hde he hK hsum
  have hV' : ∀ u, (V u)ᴴ * V u = 1 := hV
  have hr : ∑ u, ((d u : ℝ) - r u) = Rs d - Rs r := by
    unfold Rs
    rw [Finset.sum_sub_distrib]
  have h1 : (1 - de) * Rs d ≤ Rs r := by
    rw [hr] at hsum
    linarith
  refine ⟨h1, ?_⟩
  have hb : ∀ u, hsSq (Kd (Bram B V) ga u - 1) ≤ e0 * (d u : ℝ) := by
    intro u
    rw [Kd_ram_sub B V ga hV u]
    exact (hsSq_compress (V u) (hV' u) (V u) (hV' u) _).trans (hK u)
  have hTd := Rs_nonneg d
  have h2 : Rs d ≤ 2 * Rs r := by
    nlinarith [mul_nonneg (sub_nonneg.2 hde) hTd]
  unfold F2
  calc ∑ u, hsSq (Kd (Bram B V) ga u - 1)
      ≤ ∑ u, e0 * (d u : ℝ) := Finset.sum_le_sum fun u _ => hb u
    _ = e0 * Rs d := by
        unfold Rs
        rw [Finset.mul_sum]
    _ ≤ 2 * e0 * Rs r := by nlinarith [mul_le_mul_of_nonneg_left h2 he]

end RamMain

section Num

set_option maxHeartbeats 800000 in

lemma num_main {s η0 η1 a : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 4) (hη0 : -1 ≤ η0) (hη0' : η0 ≤ s / 2)
    (hη1' : η1 ≤ s / 2) (_hL : 0 ≤ 1 + η1) (ha : 0 ≤ a) (ha' : a ≤ s / 2) :
    (1 + η1) * ((1 + η0) + (1 + a) ^ 2 * s) ≤ (1 + 5 * s) * (1 - a) ^ 2 := by
  have hX0 : 0 ≤ (1 + η0) + (1 + a) ^ 2 * s :=
    add_nonneg (by linarith) (mul_nonneg (sq_nonneg _) hs0.le)
  have hsq : (1 + a) ^ 2 ≤ (1 + s / 2) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 ha') (by linarith : (0:ℝ) ≤ 2 + a + s / 2)]
  have hXY : (1 + η0) + (1 + a) ^ 2 * s ≤ (1 + s / 2) + (1 + s / 2) ^ 2 * s := by
    nlinarith [mul_le_mul_of_nonneg_right hsq hs0.le]
  have s1 : (1 + η1) * ((1 + η0) + (1 + a) ^ 2 * s) ≤ (1 + s / 2) * ((1 + η0) + (1 + a) ^ 2 * s) :=
    mul_le_mul_of_nonneg_right (by linarith) hX0
  have s2 : (1 + s / 2) * ((1 + η0) + (1 + a) ^ 2 * s)
      ≤ (1 + s / 2) * ((1 + s / 2) + (1 + s / 2) ^ 2 * s) :=
    mul_le_mul_of_nonneg_left hXY (by linarith)
  have s3 : (1 + s / 2) * ((1 + s / 2) + (1 + s / 2) ^ 2 * s) ≤ (1 + 5 * s) * (1 - s / 2) ^ 2 := by
    nlinarith [mul_nonneg hs0.le (by linarith : (0:ℝ) ≤ 1 / 4 - s),
      mul_nonneg (pow_nonneg hs0.le 3) (by linarith : (0:ℝ) ≤ 1 / 4 - s), pow_pos hs0 3, pow_pos hs0 2]
  have hsq2 : (1 - s / 2) ^ 2 ≤ (1 - a) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 ha') (by linarith : (0:ℝ) ≤ 2 - a - s / 2)]
  have s4 : (1 + 5 * s) * (1 - s / 2) ^ 2 ≤ (1 + 5 * s) * (1 - a) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq2 (by linarith)
  linarith

set_option maxHeartbeats 800000 in

lemma num_ram {s a t : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 20) (ha : 0 ≤ a) (ha' : a ≤ s / 2)
    (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    (1 + 5 * s) * (1 - a) ^ 2 ≤ (1 + 5 * s + 3 * t) * (1 - a - t ^ 2 - t * a) ^ 2 := by
  have hk : 2 * (1 + 5 * s + 3 * t) * (t + a) ≤ 3 * (1 - a) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hs) ht, mul_nonneg (sub_nonneg.2 ht') ht,
      mul_nonneg (sub_nonneg.2 ha') ht, mul_nonneg (sub_nonneg.2 hs) ha, mul_nonneg hs0.le ht]
  have hb0 : 0 ≤ 1 - a := by linarith
  have hP0 : 0 ≤ 1 + 5 * s + 3 * t := by linarith
  nlinarith [mul_nonneg (mul_nonneg ht hb0) (sub_nonneg.2 hk), mul_nonneg hP0 (sq_nonneg (t ^ 2 + t * a))]

private theorem le_div_of_mul_le_of_pos {a b c : ℝ} (hc : 0 < c) (h : a * c ≤ b) : a ≤ b / c := by
  exact (le_div_iff₀ hc).2 h

lemma num_step {T2 T1 R Dst D X L c b : ℝ} (hD : 0 < D) (hDs : 0 < Dst) (hDD : D ≤ L * Dst)
    (hX : 0 ≤ X) (hT2 : T2 ≤ R ^ 2 / Dst * X) (hb : 0 ≤ b * R) (hT1 : b * R ≤ T1)
    (hc : L * X ≤ c * b ^ 2) (hc0 : 0 ≤ c) : T2 ≤ c * T1 ^ 2 / D := by
  have ha : T2 * Dst ≤ R ^ 2 * X := by
    have h := mul_le_mul_of_nonneg_right hT2 hDs.le
    have e : R ^ 2 / Dst * X * Dst = R ^ 2 * X := by
      field_simp
    linarith
  have k1 : T2 * Dst * D ≤ R ^ 2 * X * D := mul_le_mul_of_nonneg_right ha hD.le
  have k2 : R ^ 2 * X * D ≤ R ^ 2 * X * (L * Dst) :=
    mul_le_mul_of_nonneg_left hDD (mul_nonneg (sq_nonneg R) hX)
  have k3 : R ^ 2 * (L * X) ≤ R ^ 2 * (c * b ^ 2) := mul_le_mul_of_nonneg_left hc (sq_nonneg R)
  have k3' := mul_le_mul_of_nonneg_right k3 hDs.le
  have k4 : (b * R) ^ 2 ≤ T1 ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hT1) (by linarith : (0:ℝ) ≤ T1 + b * R)]
  have k5 : c * (b * R) ^ 2 ≤ c * T1 ^ 2 := mul_le_mul_of_nonneg_left k4 hc0
  have k5' := mul_le_mul_of_nonneg_right k5 hDs.le
  have k6 : T2 * D * Dst ≤ c * T1 ^ 2 * Dst := by nlinarith
  have key : T2 * D ≤ c * T1 ^ 2 := le_of_mul_le_mul_right k6 hDs
  exact le_div_of_mul_le_of_pos hD key

end Num

section Final

variable {ι : Type} [Fintype ι] {D : ℕ} {d r : ι → ℕ}

private theorem mul_le_of_div_le_of_pos {a b c : ℝ} (hc : 0 < c) (h : a / c ≤ b) : a ≤ b * c := by
  exact (div_le_iff₀ hc).1 h

lemma cor_common (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u)
    {Dstar sg η0 η1 e0 : ℝ} (hD : 0 < Dstar) (hs0 : 0 < sg) (hs : sg ≤ 1 / 4)
    (hR : Dstar / sg ≤ Rs d) (hη0 : -1 ≤ η0) (he : 0 ≤ e0) (ha' : Real.sqrt e0 ≤ sg / 2)
    (hS : InputS B ga Dstar η0 η1 e0) :
    0 < (D : ℝ) ∧ 0 ≤ 1 + η1 ∧ 0 < Rs d ∧
    (Qm B ga * Qm B ga).trace.re
      ≤ Rs d ^ 2 / Dstar * ((1 + η0) + (1 + Real.sqrt e0) ^ 2 * sg) ∧
    (1 - Real.sqrt e0) * Rs d ≤ (Qm B ga).trace.re := by
  obtain ⟨hP, hK, hDD⟩ := hS
  have hT : 0 < Rs d := lt_of_lt_of_le (div_pos hD hs0) hR
  have hae : Real.sqrt e0 ≤ 1 / 8 := by linarith
  have hF1 := trQ_lower B ga hga he hK
  have hDpos : 0 < (D : ℝ) := by
    rcases Nat.eq_zero_or_pos D with h0 | h0
    · exfalso
      subst h0
      have h2 : (Qm B ga).trace = 0 := by simp [Matrix.trace]
      rw [h2, Complex.zero_re] at hF1
      have := mul_pos (by linarith : (0:ℝ) < 1 - Real.sqrt e0) hT
      linarith
    · exact_mod_cast h0
  have hL : 0 ≤ 1 + η1 := by
    by_contra h
    push_neg at h
    have h1 := mul_neg_of_neg_of_pos h hD
    linarith
  have hF2 := trQsq_upper B ga hga hD hη0 he hP hK
  have hDle : Dstar ≤ Rs d * sg := mul_le_of_div_le_of_pos hs0 hR
  have hTT : Rs d ≤ Rs d ^ 2 / Dstar * sg := by
    rw [div_mul_eq_mul_div]
    apply le_div_of_mul_le_of_pos hD
    nlinarith [mul_le_mul_of_nonneg_left hDle hT.le]
  have he2 : Rs d ^ 2 / Dstar * ((1 + η0) + (1 + Real.sqrt e0) ^ 2 * sg)
      = (1 + η0) * Rs d ^ 2 / Dstar + (1 + Real.sqrt e0) ^ 2 * (Rs d ^ 2 / Dstar * sg) := by
    ring
  have hm := mul_le_mul_of_nonneg_left hTT (sq_nonneg (1 + Real.sqrt e0))
  refine ⟨hDpos, hL, hT, ?_, hF1⟩
  rw [he2]
  linarith

set_option maxHeartbeats 800000 in

theorem compressTraceSquareBound : CompressTraceSquareBound := by
  intro ι _ D d r B V ga Dstar sg η0 η1 e0 de hV hga hD hs0 hs hR hη0 hη0' hη1' he ha' hde0 hde hsum hS
  have hV' : ∀ u, (V u)ᴴ * V u = 1 := hV
  have hS' := hS
  obtain ⟨hP, hK, hDD⟩ := hS'
  obtain ⟨hDpos, hL, hT, hF2, hF1⟩ :=
    cor_common B ga hga hD hs0 (by linarith) hR hη0 he ha' hS
  have hlow := compressTraceLowerBound ι D d r B V ga de e0 hV hga hde0 he hK hsum
  have hT2c : (Qm (Bram B V) ga * Qm (Bram B V) ga).trace.re
      ≤ (Qm B ga * Qm B ga).trace.re := by
    rw [trace_Qm_sq (Bram B V) ga hga, trace_Qm_sq B ga hga,
      Complex.ofReal_re, Complex.ofReal_re]
    refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun u' _ => ?_
    rw [Kp_ram B V ga u u']
    exact hsSq_compress (V u) (hV' u) (V u') (hV' u') _
  have ht0 := Real.sqrt_nonneg de
  have ha0 := Real.sqrt_nonneg e0
  have hsq : Real.sqrt de ^ 2 = de := Real.sq_sqrt hde0
  have ht1 : Real.sqrt de ≤ 1 / 2 := by nlinarith
  have hmul : Real.sqrt (de * e0) = Real.sqrt de * Real.sqrt e0 := Real.sqrt_mul hde0 e0
  have hT1' : (1 - Real.sqrt e0 - Real.sqrt de ^ 2 - Real.sqrt de * Real.sqrt e0) * Rs d
      ≤ (Qm (Bram B V) ga).trace.re := by
    rw [hmul] at hlow
    rw [hsq]
    linarith
  have hb0 : 0 ≤ (1 - Real.sqrt e0 - Real.sqrt de ^ 2 - Real.sqrt de * Real.sqrt e0) * Rs d := by
    refine mul_nonneg ?_ hT.le
    nlinarith [mul_nonneg (sub_nonneg.2 ht1) ht0, mul_nonneg (sub_nonneg.2 ht1) ha0]
  have hX0 : 0 ≤ (1 + η0) + (1 + Real.sqrt e0) ^ 2 * sg :=
    add_nonneg (by linarith) (mul_nonneg (sq_nonneg _) hs0.le)
  have hc1 := num_main hs0 (by linarith : sg ≤ 1 / 4) hη0 hη0' hη1' hL ha0 ha'
  have hc2 := num_ram hs0 hs ha0 ha' ht0 ht1
  unfold F1
  exact num_step hDpos hD hDD hX0 (hT2c.trans hF2) hb0 hT1' (by linarith [hc1, hc2])
    (by linarith)

end Final

end

end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
