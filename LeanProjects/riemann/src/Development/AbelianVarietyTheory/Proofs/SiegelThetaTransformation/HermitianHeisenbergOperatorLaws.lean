import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThHEqThSDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionUnitaryGroupTestFunctionsStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.HeisH

noncomputable section

section Cplx
variable {n N : ℕ}

theorem expo_key {Ji Jp W Z K : Matrix (Fin N) (Fin N) ℂ}
    {P Q P' Q' w : Matrix (Fin n) (Fin N) ℂ} {Ps Qs Ps' Qs' u : Matrix (Fin N) (Fin n) ℂ}
    (hr : (Q + P * Z) * Ji = Q' + P' * W) (hs : Jp * (Qs + Z * Ps) = Qs' + W * Ps')
    (hrK : (Q + P * Z) * K = P - P' * Jp)
    (hKs : K * (Qs + Z * Ps) = Ps - Ji * Ps') :
    2 * ((P' * W * Ps').trace + (P' * (Jp * u)).trace + (w * Ji * Ps').trace) +
      ((Q' * Ps').trace + (P' * Qs').trace) +
      2 * ((w + Q + P * Z) * K * (u + Qs + Z * Ps)).trace =
    2 * (w * K * u).trace + (2 * ((P * Z * Ps).trace + (P * u).trace + (w * Ps).trace) +
      ((Q * Ps).trace + (P * Qs).trace)) := by
  have e0 : (w + Q + P * Z) * K * (u + Qs + Z * Ps) = w * K * u + w * (K * (Qs + Z * Ps)) +
      (Q + P * Z) * K * u + (Q + P * Z) * K * (Qs + Z * Ps) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]; abel
  have e1 : (Q + P * Z) * K * (Qs + Z * Ps) = P * Qs + P * Z * Ps - (P' * Qs' + P' * W * Ps') := by
    rw [hrK, Matrix.sub_mul, Matrix.mul_assoc P' Jp, hs]
    simp only [Matrix.mul_add, Matrix.mul_assoc]
  have e2 : (Q + P * Z) * K * (Qs + Z * Ps) = Q * Ps + P * Z * Ps - (Q' * Ps' + P' * W * Ps') := by
    rw [Matrix.mul_assoc, hKs, Matrix.mul_sub, ← Matrix.mul_assoc, hr]
    simp only [Matrix.add_mul]
  have t0 := congrArg Matrix.trace e0
  have t1 := congrArg Matrix.trace e1
  have t2 := congrArg Matrix.trace e2
  rw [hKs, hrK] at t0
  rw [hrK] at t1 t2
  simp only [trace_add, trace_sub, Matrix.mul_sub w, Matrix.sub_mul _ _ u, Matrix.mul_assoc] at t0 t1 t2 ⊢
  linear_combination 2 * t0 + t1 + t2

theorem lin_key {A B C D Z : Matrix (Fin N) (Fin N) ℂ} (P' Q' : Matrix (Fin n) (Fin N) ℂ)
    (h1 : Aᴴ * C = Cᴴ * A) (h2 : Aᴴ * D = Cᴴ * B + 1) (h3 : Dᴴ * A = Bᴴ * C + 1)
    (h4 : Bᴴ * D = Dᴴ * B) (h5 : C * Dᴴ = D * Cᴴ) (hQ : (C * Z + D).det ≠ 0) :
    ((P' * B + Q' * D) + (P' * A + Q' * C) * Z) * (C * Z + D)⁻¹ =
      Q' + P' * ((A * Z + B) * (C * Z + D)⁻¹) ∧
    (Z * Cᴴ + Dᴴ)⁻¹ * ((P' * B + Q' * D)ᴴ + Z * (P' * A + Q' * C)ᴴ) =
      Q'ᴴ + ((A * Z + B) * (C * Z + D)⁻¹) * P'ᴴ ∧
    ((P' * B + Q' * D) + (P' * A + Q' * C) * Z) * ((C * Z + D)⁻¹ * C) =
      (P' * A + Q' * C) - P' * (Z * Cᴴ + Dᴴ)⁻¹ ∧
    ((C * Z + D)⁻¹ * C) * ((P' * B + Q' * D)ᴴ + Z * (P' * A + Q' * C)ᴴ) =
      (P' * A + Q' * C)ᴴ - (C * Z + D)⁻¹ * P'ᴴ := by
  have hd := HAct.den'_act h1 h2 h3 h4 hQ
  have hJ : (C * Z + D) * (C * Z + D)⁻¹ = 1 := mul_nonsing_inv _ (Ne.isUnit hQ)
  have hJ' : (C * Z + D)⁻¹ * (C * Z + D) = 1 := nonsing_inv_mul _ (Ne.isUnit hQ)
  have r1 : ((P' * B + Q' * D) + (P' * A + Q' * C) * Z) * (C * Z + D)⁻¹ =
      Q' + P' * ((A * Z + B) * (C * Z + D)⁻¹) := by
    have : (P' * B + Q' * D) + (P' * A + Q' * C) * Z = Q' * (C * Z + D) + P' * (A * Z + B) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]; abel
    rw [this, Matrix.add_mul, Matrix.mul_assoc, hJ, Matrix.mul_one, Matrix.mul_assoc]
  set W := (A * Z + B) * (C * Z + D)⁻¹ with hW
  have e1 : W * (C * Z + D) = A * Z + B := by
    rw [hW, Matrix.mul_assoc, hJ', Matrix.mul_one]
  have e2 : (Z * Cᴴ + Dᴴ) * (A - W * C) = 1 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hd]
    have e : (Z * Cᴴ + Dᴴ) * A - (Z * Aᴴ + Bᴴ) * C =
      Z * (Cᴴ * A) + Dᴴ * A - (Z * (Aᴴ * C) + Bᴴ * C) := by noncomm_ring
    rw [e, h1, h3]
    noncomm_ring
  have i2 : (Z * Cᴴ + Dᴴ)⁻¹ = A - W * C := inv_eq_right_inv e2
  have i2' : (Z * Cᴴ + Dᴴ)⁻¹ * (Z * Cᴴ + Dᴴ) = 1 := by rw [i2]; exact mul_eq_one_comm.1 e2
  have e3 : (Aᴴ - Cᴴ * W) * (C * Z + D) = 1 := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, e1]
    have e : Aᴴ * (C * Z + D) - Cᴴ * (A * Z + B) =
      (Aᴴ * C) * Z + Aᴴ * D - ((Cᴴ * A) * Z + Cᴴ * B) := by noncomm_ring
    rw [e, h1, h2]
    noncomm_ring
  have i3 : (C * Z + D)⁻¹ = Aᴴ - Cᴴ * W := inv_eq_left_inv e3
  have s0 : (P' * B + Q' * D)ᴴ + Z * (P' * A + Q' * C)ᴴ = (Z * Cᴴ + Dᴴ) * (Q'ᴴ + W * P'ᴴ) := by
    rw [Matrix.mul_add (Z * Cᴴ + Dᴴ), ← Matrix.mul_assoc, hd]
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_assoc]
    abel
  have k : (C * Z + D)⁻¹ * C * (Z * Cᴴ + Dᴴ) = Cᴴ := by
    have : C * (Z * Cᴴ + Dᴴ) = (C * Z + D) * Cᴴ := by
      rw [Matrix.mul_add, h5, Matrix.add_mul, Matrix.mul_assoc]
    rw [Matrix.mul_assoc, this, ← Matrix.mul_assoc, hJ', Matrix.one_mul]
  refine ⟨r1, ?_, ?_, ?_⟩
  · rw [s0, ← Matrix.mul_assoc, i2', Matrix.one_mul]
  · rw [← Matrix.mul_assoc, r1, i2]
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc]; abel
  · rw [s0, ← Matrix.mul_assoc, k, i3]
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.mul_add, Matrix.sub_mul,
      Matrix.mul_assoc]
    abel

theorem of_mulVec (A : Matrix (Fin N) (Fin N) ℂ) (w : Matrix (Fin n) (Fin N) ℂ) :
    (Matrix.of fun k => A *ᵥ w k) = (A * wᵀ)ᵀ := by
  ext k a
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem of_vecMul (A : Matrix (Fin N) (Fin N) ℂ) (w : Matrix (Fin n) (Fin N) ℂ) :
    (Matrix.of fun k => w k ᵥ* A) = w * A := by
  ext k a
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]

theorem sum_rows (K : Matrix (Fin N) (Fin N) ℂ) (z w : Matrix (Fin n) (Fin N) ℂ) :
    ∑ k, w k ⬝ᵥ K *ᵥ z k = (w * K * zᵀ).trace := by
  rw [Matrix.mul_assoc]
  rfl

theorem shift_transpose (z P Q : Matrix (Fin n) (Fin N) ℂ) (Z : Matrix (Fin N) (Fin N) ℂ) :
    (z + Q.map conj + P.map conj * Zᵀ)ᵀ = zᵀ + Qᴴ + Z * Pᴴ := by
  rw [transpose_add, transpose_add, transpose_mul, transpose_transpose]
  rfl

end Cplx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}

omit [IsCMField E] in

theorem trace_eq (hΨ : IsType Ψ) (t : E) :
    ((Algebra.trace ℚ E t : ℚ) : ℂ) = ∑ τ : Ψ, (τ.1 t + conj (τ.1 t)) := by
  have h := trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := t)
  rw [eq_ratCast] at h
  rw [h, ← Equiv.sum_comp (RingHom.equivRatAlgHom (R := E) (S := ℂ))]
  exact Dict.sum_type hΨ fun σ => σ t

def pairT (b x : Matrix (Fin n) (Fin N) E) : ℚ := Algebra.trace ℚ E (∑ k, ∑ a, b k a * cc (x k a))

theorem pairT_eq (hΨ : IsType Ψ) (b x : Matrix (Fin n) (Fin N) E) :
    ((pairT b x : ℚ) : ℂ) = ∑ τ : Ψ, ((b.map τ.1 * (x.map τ.1)ᴴ).trace +
      (x.map τ.1 * (b.map τ.1)ᴴ).trace) := by
  rw [pairT, trace_eq hΨ]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [Matrix.trace, Matrix.mul_apply, Base.map_cc, mul_comm]

theorem pairT_add (b x y : Matrix (Fin n) (Fin N) E) : pairT b (x + y) = pairT b x + pairT b y := by
  simp [pairT, cc, mul_add, Finset.sum_add_distrib]

theorem heisH_apply (d b : Matrix (Fin n) (Fin N) E) (φ : Matrix (Fin n) (Fin N) E → ℂ)
    (x : Matrix (Fin n) (Fin N) E) :
    heisH d b φ x = φ (x - d) * cexp (π * I * (2 * (pairT b x : ℂ) - pairT b d)) := by
  have : (∑ k, ∑ a, b k a * (2 * cc (x k a) - cc (d k a))) =
      (2 : ℚ) • (∑ k, ∑ a, b k a * cc (x k a)) - ∑ k, ∑ a, b k a * cc (d k a) := by
    rw [two_smul]
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => by ring
  rw [heisH, this, map_sub, map_smul, smul_eq_mul]
  simp [pairT]

theorem isSB_heisH (d b : Matrix (Fin n) (Fin N) E) {φ : Matrix (Fin n) (Fin N) E → ℂ}
    (hφ : IsSB φ) : IsSB (heisH d b φ) := by
  obtain ⟨R, hR, hs, hp⟩ := hφ
  obtain ⟨M, hM, h⟩ := Dict.exists_den (fun p : Bool × Fin n × Fin N =>
    if p.1 then d p.2.1 p.2.2 else b p.2.1 p.2.2)
  have hd : ∀ k a, IsIntegral ℤ ((M : E) * d k a) := fun k a => by
    simpa using h (true, k, a)
  have hb : ∀ k a, IsIntegral ℤ ((M : E) * b k a) := fun k a => by
    simpa using h (false, k, a)
  have c : ∀ k : ℕ, IsIntegral ℤ (k : E) := fun k => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := (k : ℤ))
  refine ⟨R * M, by positivity, fun x hx k a => ?_, fun x y hy => ?_⟩
  · rw [heisH_apply] at hx
    have h1 := hs _ (left_ne_zero_of_mul hx) k a
    have := ((c M).mul h1).add ((c R).mul (hd k a))
    have e : (((R * M : ℕ) : E) • x) k a = M * ((R : E) • (x - d)) k a + R * (M * d k a) := by
      simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Nat.cast_mul]; ring
    rw [e]; exact this
  · rw [heisH_apply, heisH_apply, pairT_add]
    have e : x + ((R * M : ℕ) : E) • y - d = x - d + (R : E) • ((M : E) • y) := by
      rw [smul_smul, Nat.cast_mul]; abel
    rw [e, hp _ ((M : E) • y) (fun k a => (c M).mul (hy k a))]
    congr 1
    have hi : IsIntegral ℤ (pairT b (((R * M : ℕ) : E) • y)) := by
      refine Algebra.isIntegral_trace (IsIntegral.sum _ fun k _ => IsIntegral.sum _ fun a _ => ?_)
      have := (c R).mul ((hb k a).mul (Base.isIntegral_cc (hy k a)))
      convert this using 1
      simp only [Matrix.smul_apply, smul_eq_mul, Nat.cast_mul, cc, map_mul, map_natCast]; ring
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
    rw [← hm, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨m, ?_⟩
    simp only [eq_intCast]
    push_cast
    ring

theorem thH_heisH (hΨ : IsType Ψ) (d b : Matrix (Fin n) (Fin N) E)
    (φ : Matrix (Fin n) (Fin N) E → ℂ) (Z : CM Ψ N N) (z z' : CM Ψ n N) :
    thH Ψ (heisH d b φ) Z z z' = cexp (2 * π * I * expo Ψ d Z z z' + π * I * (pairT b d : ℂ)) *
      thH Ψ φ Z (fun τ => z τ + (b.map τ.1).map conj + (d.map τ.1).map conj * (Z τ)ᵀ)
        (fun τ => z' τ + b.map τ.1 + d.map τ.1 * Z τ) := by
  unfold thH
  rw [← tsum_mul_left, ← (Equiv.addRight d).tsum_eq]
  refine tsum_congr fun x => ?_
  rw [Equiv.coe_addRight, heisH_apply, add_sub_cancel_right, mul_assoc, mul_left_comm _ (φ x),
    ← Complex.exp_add, ← Complex.exp_add, pairT_add]
  congr 2
  have : expo Ψ (x + d) Z z z' + pairT b x = expo Ψ d Z z z' + expo Ψ x Z
      (fun τ => z τ + (b.map τ.1).map conj + (d.map τ.1).map conj * (Z τ)ᵀ)
      (fun τ => z' τ + b.map τ.1 + d.map τ.1 * Z τ) := by
    simp only [Base.expo_eq_trace, pairT_eq hΨ, ← Finset.sum_add_distrib, shift_transpose]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Matrix.map_add _ (map_add τ.1)]
    simp only [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, trace_add, Matrix.mul_assoc]
    ring
  push_cast
  linear_combination 2 * π * I * this

theorem cols_eq {γ : M2 E N} (hγ : γ ∈ UU E N) (d b : Matrix (Fin n) (Fin N) E) :
    d = (fromCols d b * γ⁻¹).toCols₁ * γ.toBlocks₁₁ + (fromCols d b * γ⁻¹).toCols₂ * γ.toBlocks₂₁ ∧
    b = (fromCols d b * γ⁻¹).toCols₁ * γ.toBlocks₁₂ + (fromCols d b * γ⁻¹).toCols₂ * γ.toBlocks₂₂ := by
  have h : fromCols d b * γ⁻¹ * γ = fromCols d b := by
    rw [Matrix.mul_assoc, nonsing_inv_mul _ (HAct.group_part hγ).1, Matrix.mul_one]
  generalize fromCols d b * γ⁻¹ = X at h ⊢
  rw [← fromCols_toCols X, ← fromBlocks_toBlocks γ, fromCols_mul_fromBlocks] at h
  obtain ⟨h1, h2⟩ := fromCols_inj h
  exact ⟨h1.symm, h2.symm⟩

theorem transH_heisH (hΨ : IsType Ψ) {γ : M2 E N} (hγ : γ ∈ UU E N)
    (d' b' : Matrix (Fin n) (Fin N) E) {φ ψ : Matrix (Fin n) (Fin N) E → ℂ}
    (H : TransH Ψ γ φ ψ) :
    TransH Ψ γ (heisH (d' * γ.toBlocks₁₁ + b' * γ.toBlocks₂₁)
      (d' * γ.toBlocks₁₂ + b' * γ.toBlocks₂₂) φ) (heisH d' b' ψ) := by
  intro Z hZ z z'
  have hb := fun τ : Ψ => HAct.blocks (HAct.map_blocks τ.1 γ ▸ HAct.map_mem τ.1 hγ)
  have hQ : ∀ τ, (hDen Ψ γ Z τ).det ≠ 0 := fun τ =>
    HAct.det_ne (hb τ).1 (hb τ).2.1 (hb τ).2.2.1 (hb τ).2.2.2 (hZ τ)
  have h5 : ∀ τ : Ψ, γ.toBlocks₂₁.map τ.1 * (γ.toBlocks₂₂.map τ.1)ᴴ =
      γ.toBlocks₂₂.map τ.1 * (γ.toBlocks₂₁.map τ.1)ᴴ := fun τ => by
    have h := HAct.map_mem τ.1 (HAct.group_part hγ).2.2.1
    rw [HAct.map_ccT, HAct.map_blocks τ.1 γ, fromBlocks_conjTranspose] at h
    simpa using (HAct.blocks h).2.2.2
  set d := d' * γ.toBlocks₁₁ + b' * γ.toBlocks₂₁ with hd
  set b := d' * γ.toBlocks₁₂ + b' * γ.toBlocks₂₂ with hbb
  have md : ∀ τ : Ψ, d.map τ.1 = d'.map τ.1 * γ.toBlocks₁₁.map τ.1 +
      b'.map τ.1 * γ.toBlocks₂₁.map τ.1 := fun τ => by
    rw [hd, Matrix.map_add _ (map_add τ.1), Matrix.map_mul, Matrix.map_mul]
  have mb : ∀ τ : Ψ, b.map τ.1 = d'.map τ.1 * γ.toBlocks₁₂.map τ.1 +
      b'.map τ.1 * γ.toBlocks₂₂.map τ.1 := fun τ => by
    rw [hbb, Matrix.map_add _ (map_add τ.1), Matrix.map_mul, Matrix.map_mul]
  have L : ∀ τ : Ψ,
      (b.map τ.1 + d.map τ.1 * Z τ) * (hDen Ψ γ Z τ)⁻¹ = b'.map τ.1 + d'.map τ.1 * hAct Ψ γ Z τ ∧
      (hDen' Ψ γ Z τ)⁻¹ * ((b.map τ.1)ᴴ + Z τ * (d.map τ.1)ᴴ) =
        (b'.map τ.1)ᴴ + hAct Ψ γ Z τ * (d'.map τ.1)ᴴ ∧
      (b.map τ.1 + d.map τ.1 * Z τ) * ((hDen Ψ γ Z τ)⁻¹ * γ.toBlocks₂₁.map τ.1) =
        d.map τ.1 - d'.map τ.1 * (hDen' Ψ γ Z τ)⁻¹ ∧
      ((hDen Ψ γ Z τ)⁻¹ * γ.toBlocks₂₁.map τ.1) * ((b.map τ.1)ᴴ + Z τ * (d.map τ.1)ᴴ) =
        (d.map τ.1)ᴴ - (hDen Ψ γ Z τ)⁻¹ * (d'.map τ.1)ᴴ := fun τ => by
    rw [md, mb]
    exact lin_key _ _ (hb τ).1 (hb τ).2.1 (hb τ).2.2.1 (hb τ).2.2.2 (h5 τ) (hQ τ)
  have H1 := H Z hZ (fun τ => z τ + (b.map τ.1).map conj + (d.map τ.1).map conj * (Z τ)ᵀ)
    (fun τ => z' τ + b.map τ.1 + d.map τ.1 * Z τ)
  rw [thH_heisH hΨ, thH_heisH hΨ, ← mul_assoc]
  have a1 : (fun τ : Ψ => (Matrix.of fun k => (hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k) +
      (b'.map τ.1).map conj + (d'.map τ.1).map conj * (hAct Ψ γ Z τ)ᵀ) =
      fun τ : Ψ => Matrix.of fun k => (hDen' Ψ γ Z τ)⁻¹ *ᵥ
        (z τ + (b.map τ.1).map conj + (d.map τ.1).map conj * (Z τ)ᵀ) k := by
    funext τ
    apply transpose_injective
    rw [shift_transpose, of_mulVec, of_mulVec, transpose_transpose, transpose_transpose,
      shift_transpose, add_assoc, add_assoc, Matrix.mul_add, (L τ).2.1]
  have a2 : (fun τ : Ψ => (Matrix.of fun k => z' τ k ᵥ* (hDen Ψ γ Z τ)⁻¹) +
      b'.map τ.1 + d'.map τ.1 * hAct Ψ γ Z τ) =
      fun τ : Ψ => Matrix.of fun k => (z' τ + b.map τ.1 + d.map τ.1 * Z τ) k ᵥ*
        (hDen Ψ γ Z τ)⁻¹ := by
    funext τ
    rw [of_vecMul, of_vecMul, add_assoc, add_assoc, Matrix.add_mul, (L τ).1]
  rw [a1, a2, H1, ← mul_assoc]
  congr 1
  unfold hFac
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← Complex.exp_sum, ← Complex.exp_sum,
    mul_left_comm, mul_assoc (∏ τ, (hDen Ψ γ Z τ).det ^ n), ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  simp only [Base.expo_eq_trace, pairT_eq hΨ, sum_rows, shift_transpose, of_mulVec, of_vecMul,
    transpose_transpose, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have := expo_key (w := z' τ) (u := (z τ)ᵀ) (L τ).1 (L τ).2.1
    (L τ).2.2.1 (L τ).2.2.2
  linear_combination π * I * this

end

end GlobalTheory.SW.HeisH

open GlobalTheory.SW.HeisH in

theorem GlobalTheory.SW.heisH_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ (d b : Matrix (Fin n) (Fin N) E) (φ : Matrix (Fin n) (Fin N) E → ℂ), IsSB φ → IsSB (heisH d b φ) ∧ (∀ Z ∈ Hn Ψ N, ∀ z z' : CM Ψ n N, thH Ψ (heisH d b φ) Z z z' = cexp (2 * π * I * expo Ψ d Z z z' + π * I * ((Algebra.trace ℚ E (∑ k, ∑ a, b k a * cc (d k a)) : ℚ) : ℂ)) * thH Ψ φ Z (fun τ => z τ + (b.map τ.1).map conj + (d.map τ.1).map conj * (Z τ)ᵀ) (fun τ => z' τ + b.map τ.1 + d.map τ.1 * Z τ)) ∧ ∀ γ ∈ UU E N, weil Ψ γ (heisH d b φ) = heisH (Matrix.fromCols d b * γ⁻¹).toCols₁ (Matrix.fromCols d b * γ⁻¹).toCols₂ (weil Ψ γ φ) := by
  intro E _ _ _ Ψ hΨ n N hn d b φ hφ
  refine ⟨isSB_heisH d b hφ, fun Z _ z z' => thH_heisH hΨ d b φ Z z z', fun γ hγ => ?_⟩
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E Ψ hΨ n N hn γ hγ φ hφ
  have h3 := transH_heisH hΨ hγ (fromCols d b * γ⁻¹).toCols₁ (fromCols d b * γ⁻¹).toCols₂ h2
  rw [← (cols_eq hγ d b).1, ← (cols_eq hγ d b).2] at h3
  exact ((GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E Ψ hΨ n N hn γ hγ _ (isSB_heisH d b hφ)).2.2.1 _ (isSB_heisH _ _ h1) h3).symm
