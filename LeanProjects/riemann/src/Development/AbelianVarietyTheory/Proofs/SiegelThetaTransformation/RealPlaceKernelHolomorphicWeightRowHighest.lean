import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PolyDerivVanishesOfTranslationInvariance
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumPrincipalTorusAtOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DblZMemHn

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)

namespace GlobalTheory.KernHol

noncomputable section

section Alg

variable {r : ℕ}

theorem anti_inv (G W W' : Matrix (Fin r) (Fin r) ℂ) (hG : IsUnit G.det)
    (h : W * G⁻¹ * W = W' * G⁻¹ * W') (hY : IsUnit (W + W').det) :
    W * (W + W')⁻¹ * G + G * (W + W')⁻¹ * W = G := by
  have k : W * G⁻¹ * (W + W') = (W + W') * G⁻¹ * W' := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, h, add_comm]
  have k2 : G * (W + W')⁻¹ * W = W' * (W + W')⁻¹ * G := by
    calc _ = G * (W + W')⁻¹ * (W * G⁻¹ * (W + W')) * (W + W')⁻¹ * G := by
          simp only [Matrix.mul_assoc]
          rw [mul_nonsing_inv_cancel_left _ _ hY, nonsing_inv_mul _ hG, Matrix.mul_one]
      _ = _ := by
          rw [k]
          simp only [Matrix.mul_assoc]
          rw [nonsing_inv_mul_cancel_left _ _ hY, mul_nonsing_inv_cancel_left _ _ hG]
  rw [k2, ← Matrix.add_mul, ← Matrix.add_mul, mul_nonsing_inv _ hY, Matrix.one_mul]

theorem block_zero (L A x G P Q : Matrix (Fin r) (Fin r) ℂ) (hL : IsUnit L.det) (hA : IsUnit A.det)
    (hx : IsUnit x.det) (h1 : P + Q = 1) (hPQ : P * Q = 0) (hQP : Q * P = 0) (hP : Pᵀ = P)
    (e1 : Q * L = Q * x⁻¹) (e2 : P * A = P * (xᵀ * G)) : P * (L⁻¹ᵀ * G * A⁻¹) * Q = 0 := by
  have a1 : Q * (x⁻¹ * L⁻¹) = Q := by
    rw [← Matrix.mul_assoc, ← e1, mul_nonsing_inv_cancel_right _ _ hL]
  have a2 : x⁻¹ * L⁻¹ * P = P * (x⁻¹ * L⁻¹ * P) := by
    calc _ = (P + Q) * (x⁻¹ * L⁻¹) * P := by rw [h1, Matrix.one_mul]
      _ = _ := by rw [Matrix.add_mul, a1, Matrix.add_mul, hQP, add_zero, Matrix.mul_assoc]
  have a3 : L⁻¹ * P = x * P * (x⁻¹ * L⁻¹ * P) := by
    rw [Matrix.mul_assoc x, ← a2, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hx]
  have a4 : P * L⁻¹ᵀ = (x⁻¹ * L⁻¹ * P)ᵀ * (P * xᵀ) := by
    have := congrArg transpose a3
    rwa [transpose_mul, transpose_mul (x * P), transpose_mul x, hP] at this
  calc _ = (P * L⁻¹ᵀ) * G * A⁻¹ * Q := by simp only [Matrix.mul_assoc]
    _ = (x⁻¹ * L⁻¹ * P)ᵀ * (P * (xᵀ * G) * A⁻¹ * Q) := by rw [a4]; simp only [Matrix.mul_assoc]
    _ = 0 := by rw [← e2, mul_nonsing_inv_cancel_right _ _ hA, hPQ, Matrix.mul_zero]

theorem sign_comm (L A x y G P Q : Matrix (Fin r) (Fin r) ℂ) (hL : IsUnit L.det) (hA : IsUnit A.det)
    (hx : IsUnit x.det) (hy : IsUnit y.det) (h1 : P + Q = 1) (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (hP : Pᵀ = P) (hQ : Qᵀ = Q) (e1 : Q * L = Q * x⁻¹) (e2 : P * A = P * (xᵀ * G))
    (e3 : Q * A = Q * y⁻¹) (e4 : P * L = P * (yᵀ * Gᵀ)) :
    (Q - P) * (L⁻¹ᵀ * G * A⁻¹) = (L⁻¹ᵀ * G * A⁻¹) * (Q - P) := by
  have b1 := block_zero L A x G P Q hL hA hx h1 hPQ hQP hP e1 e2
  have b2 := congrArg transpose (block_zero A L y Gᵀ P Q hA hL hy h1 hPQ hQP hP e3 e4)
  simp only [transpose_mul, transpose_transpose, hP, hQ, transpose_zero] at b2
  rw [← Matrix.mul_assoc (L⁻¹ᵀ), ← Matrix.mul_assoc Q] at b2
  generalize L⁻¹ᵀ * G * A⁻¹ = M at b1 b2
  calc _ = (Q - P) * M * (P + Q) := by rw [h1, Matrix.mul_one]
    _ = (P + Q) * M * (Q - P) := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, b1, b2]
        abel
    _ = _ := by rw [h1, Matrix.one_mul]

theorem anti_exponent (G L A S : Matrix (Fin r) (Fin r) ℂ) (a : ℂ) (hG : IsUnit G.det)
    (hH : Gᴴ = G) (hL : IsUnit L.det) (hS : Sᵀ = S) (hSS : S * S = 1)
    (hc : S * (L⁻¹ᵀ * G * A⁻¹) = (L⁻¹ᵀ * G * A⁻¹) * S) (ha : conj a = -a)
    (hY : IsUnit (imH (a • ((L⁻¹ * S * L)ᵀ * G))).det) :
    ((2 * I)⁻¹ * a) • (S * (L⁻¹ᵀ * G * (imH (a • ((L⁻¹ * S * L)ᵀ * G)))⁻¹ * G * A⁻¹) +
      (L⁻¹ᵀ * G * (imH (a • ((L⁻¹ * S * L)ᵀ * G)))⁻¹ * G * A⁻¹) * S) = L⁻¹ᵀ * G * A⁻¹ := by
  have hLt : IsUnit Lᵀ.det := by rwa [det_transpose]
  set W := (L⁻¹ * S * L)ᵀ * G with hW
  have hW' : W = Lᵀ * S * Lᵀ⁻¹ * G := by
    rw [hW, transpose_mul, transpose_mul, hS, transpose_nonsing_inv, ← Matrix.mul_assoc]
  clear_value W
  rw [transpose_nonsing_inv] at hc ⊢
  have w1 : W * G⁻¹ * W = G := by
    rw [hW']
    simp only [Matrix.mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hG, nonsing_inv_mul_cancel_left _ _ hLt,
      ← Matrix.mul_assoc S, hSS, Matrix.one_mul, mul_nonsing_inv_cancel_left _ _ hLt]
  have w2 : Wᴴ * G⁻¹ * Wᴴ = G := by
    have := congrArg conjTranspose w1
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_nonsing_inv, hH,
      ← Matrix.mul_assoc] at this
  have hy : imH (a • W) = ((2 * I)⁻¹ * a) • W + ((2 * I)⁻¹ * a) • Wᴴ := by
    rw [imH, conjTranspose_smul, RCLike.star_def, ha, neg_smul, sub_neg_eq_add, smul_add, smul_smul,
      smul_smul]
  rw [hy] at hY ⊢
  have k := anti_inv G _ _ hG (by simp only [Matrix.smul_mul, Matrix.mul_smul, w1, w2]) hY
  generalize (((2 * I)⁻¹ * a) • W + ((2 * I)⁻¹ * a) • Wᴴ)⁻¹ = V at k ⊢
  have s1 : S * (Lᵀ⁻¹ * G) = Lᵀ⁻¹ * W := by
    rw [hW']
    simp only [Matrix.mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hLt]
  have s2 : G * A⁻¹ * S = W * A⁻¹ := by
    rw [hW']
    simp only [Matrix.mul_assoc] at hc ⊢
    rw [hc, mul_nonsing_inv_cancel_left _ _ hLt]
  conv_rhs => rw [← k]
  calc _ = ((2 * I)⁻¹ * a) • (S * (Lᵀ⁻¹ * G) * V * G * A⁻¹ + Lᵀ⁻¹ * G * V * (G * A⁻¹ * S)) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [s1, s2]
        simp only [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul,
          Matrix.mul_smul, smul_add]

theorem split_form {p q : ℕ} (hr : p + q = r) (N M : Matrix (Fin r) (Fin r) ℂ) (t : ℂ)
    (h : t • (diagonal (fun a : Fin r => (-(sgn p a : ℝ) : ℂ)) * N +
      N * diagonal (fun a : Fin r => (-(sgn p a : ℝ) : ℂ))) = M) (α β : Fin r → ℂ) :
    t * (β ⬝ᵥ N *ᵥ α) = -(1 / 2) * (β ⬝ᵥ M *ᵥ fun a => if (a : ℕ) < p then α a else -α a) +
      t * (∑ i, ∑ j, N (rowIdx hr (.inl i)) (rowIdx hr (.inr j)) * β (rowIdx hr (.inl i)) *
        α (rowIdx hr (.inr j))) +
      t * (∑ i, ∑ j, N (rowIdx hr (.inr j)) (rowIdx hr (.inl i)) * α (rowIdx hr (.inl i)) *
        β (rowIdx hr (.inr j))) := by
  have h1 (i : Fin q) : ¬ (rowIdx hr (.inl i) : ℕ) < p := by simp
  have h2 (j : Fin p) : (rowIdx hr (.inr j) : ℕ) < p := by
    have := j.isLt; rw [rowIdx_inr]; omega
  have e (f : Fin r → ℂ) : ∑ a, f a = ∑ i, f (rowIdx hr (.inl i)) + ∑ j, f (rowIdx hr (.inr j)) := by
    rw [← (rowIdx hr).sum_comp, Fintype.sum_sum_type]
  have hB (N : Matrix (Fin r) (Fin r) ℂ) (α : Fin r → ℂ) : β ⬝ᵥ N *ᵥ α = ∑ a, ∑ b, β a * N a b * α b := by
    simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have hM (a b) : M a b = t * (-(sgn p a : ℝ) * N a b + N a b * -(sgn p b : ℝ)) := by
    rw [← h, Matrix.smul_apply, Matrix.add_apply, diagonal_mul, mul_diagonal, smul_eq_mul]
  rw [hB, hB, Finset.sum_comm (f := fun i j => N (rowIdx hr (.inr j)) (rowIdx hr (.inl i)) * _ * _)]
  simp only [e, hM, sgn, h1, h2, if_true, if_false, mul_add, Finset.mul_sum,
    Finset.sum_add_distrib]
  have c2 {m m' : ℕ} (f f' : Fin m → Fin m' → ℂ) (h : ∀ a b, f a b = f' a b) :
      ∑ a, ∑ b, f a b = ∑ a, ∑ b, f' a b := by simp only [h]
  have key (a b c d a' b' c' d' e f : ℂ) (k1 : a = a') (k2 : b' = 0) (k3 : c' = 0) (k4 : d = d')
      (k5 : b = e) (k6 : c = f) : a + b + (c + d) = a' + b' + (c' + d') + e + f := by
    rw [k1, k2, k3, k4, k5, k6]; ring
  refine key _ _ _ _ _ _ _ _ _ _ (c2 _ _ fun _ _ => ?_)
    (Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => ?_)
    (Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => ?_) (c2 _ _ fun _ _ => ?_)
    (c2 _ _ fun _ _ => ?_) (c2 _ _ fun _ _ => ?_) <;> push_cast <;> ring

end Alg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} (X : Data E r)
  (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r)

def mix (z w : Fin n → Fin g → ℂ) (τ : X.Ψ) (k : Fin n) : Fin r → ℂ := fun a =>
  if (a : ℕ) < X.p0 then z k (idx.symm (τ, a)) else w k (idx.symm (τ, a))

def kRed (x₁ x₂ : Frame X.Ψ r) (z w : Fin n → Fin g → ℂ) : ℂ :=
  ∏ τ : X.Ψ, (((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det) ^ (n / 2))⁻¹ *
    cexp (Real.pi * (I * τ.1 X.κ0) * ∑ k, ((aLin X x₁ x₂ τ)⁻¹ *ᵥ mix X idx w z τ k) ⬝ᵥ
      X.Gm.map τ.1 *ᵥ (aAnti X x₁ x₂ τ)⁻¹ *ᵥ mix X idx z (-w) τ k)

def bal (γ : X.Ψ → Fin q0 → Fin X.p0 → ℂ) (w : Fin n → Fin g → ℂ) : ℂ :=
  ∑ t, ∑ a, ∑ b, ∑ k, γ t a b * w k (idx.symm (t, rowIdx hr (.inl a))) *
    w k (idx.symm (t, rowIdx hr (.inr b)))

theorem anti_frames {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom) (τ : X.Ψ) :
    ((2 * I)⁻¹ * (τ.1 X.κ0 / 4)) • (diagonal (fun a : Fin r => (-(sgn X.p0 a : ℝ) : ℂ)) *
      ((aLin X x₁ x₂ τ)⁻¹ᵀ * X.Gm.map τ.1 * (imH (dblZ X x₁ x₂ τ))⁻¹ * X.Gm.map τ.1 *
        (aAnti X x₁ x₂ τ)⁻¹) +
      ((aLin X x₁ x₂ τ)⁻¹ᵀ * X.Gm.map τ.1 * (imH (dblZ X x₁ x₂ τ))⁻¹ * X.Gm.map τ.1 *
        (aAnti X x₁ x₂ τ)⁻¹) * diagonal (fun a : Fin r => (-(sgn X.p0 a : ℝ) : ℂ))) =
      (aLin X x₁ x₂ τ)⁻¹ᵀ * X.Gm.map τ.1 * (aAnti X x₁ x₂ τ)⁻¹ := by
  obtain ⟨-, hZ, hd⟩ := GlobalTheory.SW.dblZ_mem_Hn E r X x₁ h₁ x₂ h₂
  obtain ⟨hL, hA, -⟩ := hd τ
  let P : Matrix (Fin r) (Fin r) ℂ := diagonal fun a => if (a : ℕ) < X.p0 then 1 else 0
  let Q : Matrix (Fin r) (Fin r) ℂ := diagonal fun a => if (a : ℕ) < X.p0 then 0 else 1
  have hS : diagonal (fun a : Fin r => (-(sgn X.p0 a : ℝ) : ℂ)) = Q - P := by
    rw [diagonal_sub]
    congr 1
    funext a
    by_cases h : (a : ℕ) < X.p0 <;> simp [sgn, h]
  have hy : (mat x₂ τ).map conj * ((mat x₂ τ)⁻¹).map conj = 1 := by
    rw [← Matrix.map_mul, mul_nonsing_inv _ (h₂ τ).1.isUnit]; simp
  refine anti_exponent _ _ _ _ _ ?_ ?_ hL.isUnit (diagonal_transpose _) ?_ ?_ ?_
    (hZ τ).det_pos.ne'.isUnit
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((map_ne_zero τ.1).2 X.Gm_det).isUnit
  · ext a b
    rw [conjTranspose_apply, map_apply, map_apply, RCLike.star_def, ← PerMove.map_cc, X.Gm_herm]
  · rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    by_cases h : (a : ℕ) < X.p0 <;> simp [sgn, h]
  · rw [hS]
    refine sign_comm _ _ (mat x₁ τ) ((mat x₂ τ).map conj) _ P Q hL.isUnit hA.isUnit
      (h₁ τ).1.isUnit (isUnit_det_of_right_inverse hy) ?_ ?_ ?_ (diagonal_transpose _)
      (diagonal_transpose _) ?_ ?_ ?_ ?_
    · rw [diagonal_add, ← diagonal_one]
      congr 1
      funext a
      split_ifs <;> simp
    · rw [diagonal_mul_diagonal, ← diagonal_zero]
      congr 1
      funext a
      split_ifs <;> simp
    · rw [diagonal_mul_diagonal, ← diagonal_zero]
      congr 1
      funext a
      split_ifs <;> simp
    · ext a c
      simp only [Q, diagonal_mul, aLin, of_apply]
      split_ifs <;> simp
    · ext a c
      simp only [P, diagonal_mul, aAnti, of_apply]
      split_ifs <;> simp [mul_apply, mat]
    · rw [inv_eq_right_inv hy]
      ext a c
      simp only [Q, diagonal_mul, aAnti, of_apply]
      split_ifs <;> simp
    · ext a c
      simp only [P, diagonal_mul, aLin, of_apply]
      split_ifs <;> simp [mul_apply, mat, mul_comm]
  · have h := emb_neg_half X τ
    rw [map_neg, map_div₀, map_ofNat] at h
    have h' : τ.1 X.κ0 / 4 = -(I * (X.c τ / 4 : ℝ)) := by
      push_cast at h ⊢
      linear_combination (-1 / 2) * h
    rw [h', map_neg, map_mul, conj_I, conj_ofReal]
    ring

theorem kZero_eq {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom) :
    ∃ γ γ' : X.Ψ → Fin q0 → Fin X.p0 → ℂ, ∀ z w : Fin n → Fin g → ℂ, kZero X idx x₁ x₂ z w =
      cexp (bal X hr idx γ w) * (cexp (bal X hr idx γ' z) * kRed X idx x₁ x₂ z w) := by
  let N : X.Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => (aLin X x₁ x₂ τ)⁻¹ᵀ * X.Gm.map τ.1 *
    (imH (dblZ X x₁ x₂ τ))⁻¹ * X.Gm.map τ.1 * (aAnti X x₁ x₂ τ)⁻¹
  let s : X.Ψ → ℂ := fun τ => Real.pi * -(τ.1 X.κ0 ^ 2 / 4)
  refine ⟨fun τ i j => s τ * N τ (rowIdx hr (.inr j)) (rowIdx hr (.inl i)),
    fun τ i j => s τ * N τ (rowIdx hr (.inl i)) (rowIdx hr (.inr j)), fun z w => ?_⟩
  rw [kZero, kRed, bal, bal, Complex.exp_sum, Complex.exp_sum, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have key (D a b c d : ℂ) (h : a = b + (c + d)) :
      D * cexp a = cexp b * (cexp c * (D * cexp d)) := by
    rw [h, Complex.exp_add, Complex.exp_add]; ring
  refine key _ _ _ _ _ ?_
  have h1 (i : Fin q0) : ¬ (rowIdx hr (.inl i) : ℕ) < X.p0 := by simp
  have h2 (j : Fin X.p0) : (rowIdx hr (.inr j) : ℕ) < X.p0 := by
    have := j.isLt; rw [rowIdx_inr]; omega
  have c3 (f : Fin q0 → Fin X.p0 → Fin n → ℂ) :
      ∑ a, ∑ b, ∑ k, f a b k = ∑ k, ∑ a, ∑ b, f a b k := by
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin n)))]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [c3, c3, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := split_form hr (N τ) _ _ (anti_frames X h₁ h₂ τ) (mix X idx z w τ k) (mix X idx w z τ k)
  have e1 : (fun a : Fin r => if (a : ℕ) < X.p0 then mix X idx z w τ k a else -mix X idx z w τ k a) =
      mix X idx z (-w) τ k := by
    funext a
    by_cases h : (a : ℕ) < X.p0 <;> simp [mix, h]
  have e2 : dblz' X idx x₁ x₂ z w τ k ⬝ᵥ (imH (dblZ X x₁ x₂ τ))⁻¹ *ᵥ dblz X idx x₁ x₂ z w τ k =
      -(τ.1 X.κ0 ^ 2 / 4) * (mix X idx w z τ k ⬝ᵥ N τ *ᵥ mix X idx z w τ k) := by
    change ((τ.1 X.κ0 / 2) • (((aLin X x₁ x₂ τ)⁻¹ *ᵥ mix X idx w z τ k) ᵥ* X.Gm.map τ.1)) ⬝ᵥ
      _ *ᵥ ((-(τ.1 X.κ0 / 2)) • (X.Gm.map τ.1 *ᵥ (aAnti X x₁ x₂ τ)⁻¹ *ᵥ mix X idx z w τ k)) = _
    simp only [N, ← mulVec_mulVec]
    rw [smul_dotProduct, mulVec_smul, dotProduct_smul, ← dotProduct_mulVec,
      dotProduct_mulVec (mix X idx w z τ k), vecMul_transpose]
    simp only [smul_eq_mul]
    ring
  rw [e1, ← mulVec_mulVec (mix X idx z (-w) τ k), ← mulVec_mulVec _ (aLin X x₁ x₂ τ)⁻¹ᵀ,
    dotProduct_mulVec _ (aLin X x₁ x₂ τ)⁻¹ᵀ,
    vecMul_transpose] at h
  have m1 (z w : Fin n → Fin g → ℂ) (i) : mix X idx z w τ k (rowIdx hr (.inl i)) =
    w k (idx.symm (τ, rowIdx hr (.inl i))) := if_neg (h1 i)
  have m2 (z w : Fin n → Fin g → ℂ) (i) : mix X idx z w τ k (rowIdx hr (.inr i)) =
    z k (idx.symm (τ, rowIdx hr (.inr i))) := if_pos (h2 i)
  simp only [m1, m2] at h
  simp only [mul_assoc (s τ), ← Finset.mul_sum]
  rw [e2]
  simp only [s]
  have hI : (2 * I)⁻¹ = -I / 2 := by rw [mul_inv, inv_I]; ring
  rw [hI] at h
  have fin (F R S S' κ : ℂ) (h : -I / 2 * (κ / 4) * F =
      -(1 / 2) * R + -I / 2 * (κ / 4) * S + -I / 2 * (κ / 4) * S') : π * (-(κ ^ 2 / 4) * F) =
      π * -(κ ^ 2 / 4) * S' + (π * -(κ ^ 2 / 4) * S + π * (I * κ) * R) := by
    linear_combination (π * (-2 * I * κ)) * h - (π * κ ^ 2 / 4 * (F - S - S')) * I_mul_I
  exact fin _ _ _ _ _ h

theorem differentiableOn_kRed {x₂ : Frame X.Ψ r} (h₂ : x₂ ∈ X.dom) :
    DifferentiableOn ℂ (fun p : (Frame X.Ψ r × (Fin n → Fin g → ℂ)) × (Fin n → Fin g → ℂ) =>
      kRed X idx p.1.1 x₂ p.1.2 p.2) ((X.dom ×ˢ Set.univ) ×ˢ Set.univ) := by
  have hent (τ a c) : DifferentiableOn ℂ (fun x : Frame X.Ψ r => mat x τ a c) X.dom := by
    change DifferentiableOn ℂ (fun x : Frame X.Ψ r => x τ a c) _
    fun_prop
  have hL (τ a c) : DifferentiableOn ℂ (fun x => aLin X x x₂ τ a c) X.dom := by
    simp only [aLin, of_apply]
    split_ifs
    · exact differentiableOn_const _
    · exact RiemannRel.differentiableOn_left_inverse (fun x => mat x τ) (fun x => (mat x τ)⁻¹)
        (hent τ) (fun x hx => nonsing_inv_mul _ (hx τ).1.isUnit) a c
  have hA (τ a c) : DifferentiableOn ℂ (fun x => aAnti X x x₂ τ a c) X.dom := by
    simp only [aAnti, of_apply]
    split_ifs
    · fun_prop
    · exact differentiableOn_const _
  have hd (x) (hx : x ∈ X.dom) := (GlobalTheory.SW.dblZ_mem_Hn E r X x hx x₂ h₂).2.2
  have lift {f : Frame X.Ψ r → ℂ} (hf : DifferentiableOn ℂ f X.dom) : DifferentiableOn ℂ
      (fun p : (Frame X.Ψ r × (Fin n → Fin g → ℂ)) × (Fin n → Fin g → ℂ) => f p.1.1)
      ((X.dom ×ˢ Set.univ) ×ˢ Set.univ) :=
    hf.comp (f := fun p : (Frame X.Ψ r × (Fin n → Fin g → ℂ)) × (Fin n → Fin g → ℂ) => p.1.1)
      (by fun_prop) fun _ hp => hp.1.1
  refine CanTh.differentiableOn_prod_fun _ fun τ _ => DifferentiableOn.mul (lift
    (f := fun x => (((aLin X x x₂ τ).det * (aAnti X x x₂ τ).det) ^ (n / 2))⁻¹) ?_) ?_
  · exact (((RiemannRel.differentiableOn_det _ (hL τ)).mul
      (RiemannRel.differentiableOn_det _ (hA τ))).pow _).inv fun x hx =>
        pow_ne_zero _ (mul_ne_zero (hd x hx τ).1 (hd x hx τ).2.1)
  · have iL := fun a c => lift (RiemannRel.differentiableOn_left_inverse (fun x => aLin X x x₂ τ)
      (fun x => (aLin X x x₂ τ)⁻¹) (hL τ) (fun x hx => nonsing_inv_mul _ (hd x hx τ).1.isUnit) a c)
    have iA := fun a c => lift (RiemannRel.differentiableOn_left_inverse (fun x => aAnti X x x₂ τ)
      (fun x => (aAnti X x x₂ τ)⁻¹) (hA τ)
      (fun x hx => nonsing_inv_mul _ (hd x hx τ).2.1.isUnit) a c)
    refine (DifferentiableOn.const_mul (DifferentiableOn.fun_sum fun k _ => ?_) _).cexp
    simp only [dotProduct, mulVec]
    refine DifferentiableOn.fun_sum fun a _ => DifferentiableOn.mul
      (DifferentiableOn.fun_sum fun b _ => (iL a b).mul ?_)
      (DifferentiableOn.fun_sum fun b _ => DifferentiableOn.const_mul
        (DifferentiableOn.fun_sum fun c _ => (iA b c).mul ?_) _)
    · simp only [mix]
      split_ifs <;> fun_prop
    · simp only [mix, Pi.neg_apply]
      split_ifs <;> fun_prop

def inner₂ (Q : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (x₁ x₂ : Frame X.Ψ r) (z : Fin n → Fin g → ℂ) : ℂ :=
  polyDeriv Q (letterDir X hr idx) (kRed X idx x₁ x₂ z) 0

theorem differentiableOn_inner₂ (Q : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) {x₂ : Frame X.Ψ r}
    (h₂ : x₂ ∈ X.dom) : DifferentiableOn ℂ
      (fun p : Frame X.Ψ r × (Fin n → Fin g → ℂ) => inner₂ X hr idx Q p.1 x₂ p.2)
      (X.dom ×ˢ Set.univ) :=
  CanTh.differentiableOn_polyDeriv_param ((FourierCoefficientDomain.isOpen_dom X).prod isOpen_univ)
    (differentiableOn_kRed X idx h₂) Q _ 0

theorem differentiable_inner₂ (Q : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) {x₁ x₂ : Frame X.Ψ r}
    (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom) : Differentiable ℂ (inner₂ X hr idx Q x₁ x₂) :=
  differentiableOn_univ.1 ((differentiableOn_inner₂ X hr idx Q h₂).comp (f := fun z => (x₁, z))
    (by fun_prop) fun _ _ => ⟨h₁, trivial⟩)

theorem differentiable_kRed {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom)
    (z : Fin n → Fin g → ℂ) : Differentiable ℂ (kRed X idx x₁ x₂ z) :=
  differentiableOn_univ.1 ((differentiableOn_kRed X idx h₂).comp (f := fun w => ((x₁, z), w))
    (by fun_prop) fun _ _ => ⟨⟨h₁, trivial⟩, trivial⟩)

theorem polyDeriv_bal {Q : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)} (hQ : Harm.IsHarmonic Q)
    (γ : X.Ψ → Fin q0 → Fin X.p0 → ℂ) {F : (Fin n → Fin g → ℂ) → ℂ} (hF : Differentiable ℂ F) :
    polyDeriv Q (letterDir X hr idx) (fun w => cexp (bal X hr idx γ w) * F w) 0 =
      polyDeriv Q (letterDir X hr idx) F 0 := by
  have an {F : (Fin n → Fin g → ℂ) → ℂ} (hF : Differentiable ℂ F) : AnalyticAt ℂ F 0 :=
    SCV.analyticAt_of_differentiableOn hF.differentiableOn Filter.univ_mem
  refine GaussGauge.polyDeriv_exp_balanced_mul_dir hQ γ _ (an ?_) (fun z => ?_) (an hF)
  · unfold bal
    fun_prop
  · have h (τ ρ k) : (∑ i, z i • letterDir X hr idx i) k (idx.symm (τ, rowIdx hr ρ)) =
        z (τ, ρ, k) := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single (τ, ρ, k)]
      · simp [letterDir]
      · rintro ⟨τ', ρ', k'⟩ - hne
        by_cases hk : k = k'
        · subst hk
          have : ¬ (τ = τ' ∧ ρ = ρ') := by
            rintro ⟨rfl, rfl⟩
            exact hne rfl
          simp [letterDir, this]
        · simp [letterDir, hk]
      · simp
    simp only [bal, h]

theorem kern_eq {J : Type} [Fintype J] {P : J → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)}
    (hP : ∀ j, Harm.IsHarmonic (P j)) {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom) :
    kern X hr idx P x₁ x₂ =
      ∑ j, polyDeriv (P j) (letterDir X hr idx) (inner₂ X hr idx (barP (P j)) x₁ x₂) 0 := by
  obtain ⟨γ, γ', h⟩ := kZero_eq (n := n) X hr idx h₁ h₂
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← polyDeriv_bal X hr idx (hP j) γ' (differentiable_inner₂ X hr idx _ h₁ h₂)]
  congr 1
  funext z
  rw [funext (h z), polyDeriv_bal X hr idx (Q := barP (P j)) ((hP j).map _) γ
    ((differentiable_kRed X idx h₁ h₂ z).const_mul _)]
  exact CanTh.polyDeriv_const_mul _ _ isOpen_univ
    (differentiable_kRed X idx h₁ h₂ z).differentiableOn _ trivial

def upMat (b : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a c =>
  if (a : ℕ) < X.p0 then b τ c a else (1 : Matrix (Fin r) (Fin r) ℂ) a c

def lowMat (b : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a c =>
  if (a : ℕ) < X.p0 then (1 : Matrix (Fin r) (Fin r) ℂ) a c else (mat b τ)⁻¹ a c

section Move

variable {X} {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ)
include hb

theorem upMat_mulVec (u v : Fin r → ℂ) :
    (upMat X b τ *ᵥ fun a => if (a : ℕ) < X.p0 then u a else v a) =
      fun a : Fin r => if (a : ℕ) < X.p0 then ∑ c, b τ c a * u c else v a := by
  funext a
  simp only [mulVec, dotProduct, upMat, of_apply]
  split_ifs with h
  · refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with hc
    · rfl
    · rw [(hb τ).2 c a (by rw [Fin.lt_def]; omega), zero_mul, zero_mul]
  · rw [Finset.sum_eq_single a (fun c _ hc => by rw [one_apply_ne hc.symm, zero_mul]) (by simp)]
    simp [h]

theorem lowMat_mulVec (u v : Fin r → ℂ) :
    (lowMat X b τ *ᵥ fun a => if (a : ℕ) < X.p0 then u a else v a) =
      fun a : Fin r => if (a : ℕ) < X.p0 then u a else ∑ c, (mat b τ)⁻¹ a c * v c := by
  funext a
  simp only [mulVec, dotProduct, lowMat, of_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single a (fun c _ hc => by rw [one_apply_ne hc.symm, zero_mul]) (by simp)]
    simp [h]
  · refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with hc
    · rw [PerMove.bor_inv_tri hb τ (show c < a by rw [Fin.lt_def]; omega), zero_mul, zero_mul]
    · rfl

theorem aAnti_rmul (x₁ x₂ : Frame X.Ψ r) :
    aAnti X (rmul x₁ b) x₂ τ = upMat X b τ * aAnti X x₁ x₂ τ := by
  ext a c
  refine Eq.trans ?_ (congrFun (upMat_mulVec hb τ (fun a => ∑ d, x₁ τ d a * τ.1 (X.Gm d c))
    fun a => conj ((mat x₂ τ)⁻¹ a c)) a).symm
  simp only [aAnti, of_apply]
  split_ifs
  · simp only [rmul, mul_apply, mat, of_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · rfl

theorem aLin_rmul (x₁ x₂ : Frame X.Ψ r) :
    aLin X (rmul x₁ b) x₂ τ = lowMat X b τ * aLin X x₁ x₂ τ := by
  ext a c
  refine Eq.trans ?_ (congrFun (lowMat_mulVec hb τ (fun a => ∑ d, τ.1 (X.Gm c d) * conj (x₂ τ d a))
    fun a => (mat x₁ τ)⁻¹ a c) a).symm
  have hm : mat (rmul x₁ b) τ = mat x₁ τ * mat b τ := rfl
  simp only [aLin, of_apply, hm, Matrix.mul_inv_rev, mul_apply]

theorem det_moves : (lowMat X b τ).det * (upMat X b τ).det =
    ∏ a, rowFac X (fun τ a => b τ a a) (τ, a) := by
  rw [det_of_isUpperTriangular (M := lowMat X b τ), det_of_isLowerTriangular (upMat X b τ),
    ← Finset.prod_mul_distrib]
  · refine Finset.prod_congr rfl fun a _ => ?_
    simp only [lowMat, upMat, of_apply, rowFac]
    split_ifs
    · simp
    · simp [PerMove.bor_inv_diag hb]
  · intro a c h
    have h' : a < c := h
    simp only [upMat, of_apply]
    split_ifs
    · exact (hb τ).2 c a h'
    · exact one_apply_ne h'.ne
  · intro a c h
    have h' : c < a := h
    simp only [lowMat, of_apply]
    split_ifs
    · exact one_apply_ne h'.ne'
    · exact PerMove.bor_inv_tri hb τ h'

omit hb in

theorem borMat_mulVec (v : Fin g → ℂ) (a : Fin r) :
    ((borMat X b).submatrix idx idx *ᵥ v) (idx.symm (τ, a)) =
      ∑ c, borMat X b (τ, a) (τ, c) * v (idx.symm (τ, c)) := by
  rw [mulVec, dotProduct, ← idx.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · simp
  · intro σ _ hσ
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [submatrix_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply, borMat_of_ne X b hσ,
      zero_mul]
  · simp

omit τ in

theorem kRed_rmul (x₁ x₂ : Frame X.Ψ r) (z w : Fin n → Fin g → ℂ) :
    kRed X idx (rmul x₁ b) x₂ (fun k => (borMat X b).submatrix idx idx *ᵥ z k) w =
      (∏ p, (rowFac X (fun τ a => b τ a a) p)⁻¹) ^ (n / 2) * kRed X idx x₁ x₂ z w := by
  rw [kRed, kRed, Fintype.prod_prod_type, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hd := det_moves hb τ
  have h0 : (lowMat X b τ).det * (upMat X b τ).det ≠ 0 := by
    rw [hd]
    exact Finset.prod_ne_zero_iff.2 fun a _ =>
      rowFac_ne_zero (fun τ a => PerMove.bor_diag_ne hb τ a) _
  have e1 (w k) : mix X idx (fun k => (borMat X b).submatrix idx idx *ᵥ z k) w τ k =
      upMat X b τ *ᵥ mix X idx z w τ k := by
    refine Eq.trans ?_ (upMat_mulVec hb τ _ _).symm
    funext a
    simp only [mix]
    split_ifs with h
    · simp only [borMat_mulVec, borMat_of_lt X b τ h]
    · rfl
  have e2 (w k) : mix X idx w (fun k => (borMat X b).submatrix idx idx *ᵥ z k) τ k =
      lowMat X b τ *ᵥ mix X idx w z τ k := by
    refine Eq.trans ?_ (lowMat_mulVec hb τ _ _).symm
    funext a
    simp only [mix]
    split_ifs with h
    · rfl
    · simp only [borMat_mulVec, borMat_of_le X b τ (not_lt.1 h)]
  have i1 (M : Matrix (Fin r) (Fin r) ℂ) (v) : (upMat X b τ * M)⁻¹ *ᵥ upMat X b τ *ᵥ v = M⁻¹ *ᵥ v := by
    rw [mulVec_mulVec, Matrix.mul_inv_rev,
      nonsing_inv_mul_cancel_right _ _ (right_ne_zero_of_mul h0).isUnit]
  have i2 (M : Matrix (Fin r) (Fin r) ℂ) (v) :
      (lowMat X b τ * M)⁻¹ *ᵥ lowMat X b τ *ᵥ v = M⁻¹ *ᵥ v := by
    rw [mulVec_mulVec, Matrix.mul_inv_rev,
      nonsing_inv_mul_cancel_right _ _ (left_ne_zero_of_mul h0).isUnit]
  simp only [e1, e2, aLin_rmul hb, aAnti_rmul hb, i1, i2]
  rw [Finset.prod_inv_distrib, ← hd, det_mul, det_mul, mul_mul_mul_comm, mul_pow, mul_inv, inv_pow,
    mul_assoc]

end Move

theorem outer_rmul {c : X.Ψ → Fin q0 → ℕ} {c' : X.Ψ → Fin X.p0 → ℕ}
    {P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)} (hP : P ∈ Harm.rowHighest ℂ c c')
    (Q : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) {x x₂ u : Frame X.Ψ r} (hx : x ∈ X.dom) (h₂ : x₂ ∈ X.dom)
    (hu : u ∈ Bor X.Ψ r) :
    polyDeriv P (letterDir X hr idx) (inner₂ X hr idx Q (rmul x u) x₂) 0 =
      bchar (wtOf X hr c c' n) u * polyDeriv P (letterDir X hr idx) (inner₂ X hr idx Q x x₂) 0 := by
  have hF := differentiable_inner₂ X hr idx Q (PerMove.rmul_mem_GG hx hu) h₂
  let φ : (Fin n → Fin g → ℂ) →L[ℂ] (Fin n → Fin g → ℂ) := LinearMap.toContinuousLinearMap
    (LinearMap.pi fun k => ((borMat X u).submatrix idx idx).mulVecLin ∘ₗ LinearMap.proj k)
  have h1 : inner₂ X hr idx Q (rmul x u) x₂ ∘ φ = fun z =>
      (∏ p, (rowFac X (fun τ a => u τ a a) p)⁻¹) ^ (n / 2) * inner₂ X hr idx Q x x₂ z := by
    funext z
    refine Eq.trans ?_ (CanTh.polyDeriv_const_mul _ _ isOpen_univ
      (differentiable_kRed X idx hx h₂ z).differentiableOn _ trivial)
    exact congrArg (polyDeriv Q (letterDir X hr idx) · 0) (funext (kRed_rmul idx hu x x₂ z))
  have h2 : φ ∘ letterDir X hr idx = fun l => ∑ i, borMat X u (rowOf X hr i)
      (rowOf X hr (l.1, l.2.1)) • letterDir X hr idx (i.1, i.2, l.2.2) := by
    funext l k j
    change ((borMat X u).submatrix idx idx *ᵥ letterDir X hr idx l k) j = _
    by_cases hk : k = l.2.2
    · simp only [letterDir, hk, Pi.single_eq_same, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        mulVec_single_one, col_apply, submatrix_apply, Equiv.apply_symm_apply, Prod.mk.eta]
      rw [Finset.sum_eq_single ((rowOf X hr).symm (idx j))]
      · simp
      · intro i _ hi
        rw [Pi.single_eq_of_ne, mul_zero]
        rintro rfl
        simp at hi
      · simp
    · simp [letterDir, hk, -rowOf_apply]
  have h3 := Jet.polyDeriv_comp_clm P (letterDir X hr idx) hF φ 0
  rw [h1, map_zero, h2, polyDeriv_triangular (I2.contDiff_of_diff hF) hP
      (fun i j => borMat X u (rowOf X hr i) (rowOf X hr j)) (borMat_rowOf_eq_zero hr hu),
    CanTh.polyDeriv_const_mul _ _ isOpen_univ
      (differentiable_inner₂ X hr idx Q hx h₂).differentiableOn _ trivial,
    ← bchar_wtOf_mul hr hu c c' n] at h3
  simp only [borMat_diag hu] at h3
  rw [mul_comm (bchar _ _), mul_assoc] at h3
  exact mul_left_cancel₀ (Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _
    (rowFac_ne_zero (fun τ a => PerMove.bor_diag_ne hu τ a) _)) h3.symm

theorem kern_hol_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ) (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (m : ℕ) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), Even n → (∀ j, P j ∈ Harm.rowHighest ℂ c c') → ∀ x₂ ∈ X.dom, DifferentiableOn ℂ (fun x₁ => kern X hr idx P x₁ x₂) X.dom ∧ ∀ x₁ ∈ X.dom, ∀ b ∈ Bor X.Ψ r, kern X hr idx P (rmul x₁ b) x₂ = bchar (wtOf X hr c c' n) b * kern X hr idx P x₁ x₂ := by
  intro E _ _ _ r X g q0 hr idx n c c' m P _ hP x₂ h₂
  have hH (j) : Harm.IsHarmonic (P j) := (Harm.mem_rowHighest_iff.1 (hP j)).1
  refine ⟨DifferentiableOn.congr ?_ fun x hx => kern_eq X hr idx hH hx h₂, fun x hx b hb => ?_⟩
  · exact DifferentiableOn.fun_sum fun j _ => CanTh.differentiableOn_polyDeriv_param
      (FourierCoefficientDomain.isOpen_dom X) (differentiableOn_inner₂ X hr idx (barP (P j)) h₂) (P j) _ 0
  · rw [kern_eq X hr idx hH (PerMove.rmul_mem_GG hx hb) h₂, kern_eq X hr idx hH hx h₂,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => outer_rmul X hr idx (hP j) _ hx h₂ hb

end

end GlobalTheory.KernHol
