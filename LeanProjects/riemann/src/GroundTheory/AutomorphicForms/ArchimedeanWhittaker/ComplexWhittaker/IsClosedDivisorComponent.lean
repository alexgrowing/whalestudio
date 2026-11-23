import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.IsSmCCre

namespace GroundTheory.Automorphic.ArchWhittakerC

namespace KT

open Matrix MeasureTheory Complex Finset
open scoped Matrix.Norms.L2Operator InnerProductSpace ComplexConjugate

noncomputable def psi (n : ℕ) (q : ℤ) (i : ℕ) (k : U2) : ℂ :=
  (k : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ^ i * (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ^ (n - i) *
    (k : Matrix (Fin 2) (Fin 2) ℂ).det ^ q

theorem continuous_entry (a b : Fin 2) : Continuous fun k : U2 => (k : Matrix (Fin 2) (Fin 2) ℂ) a b :=
  (continuous_apply b).comp ((continuous_apply a).comp continuous_subtype_val)

theorem continuous_det : Continuous fun k : U2 => (k : Matrix (Fin 2) (Fin 2) ℂ).det :=
  continuous_subtype_val.matrix_det

theorem continuous_psi (n : ℕ) (q : ℤ) (i : ℕ) : Continuous (psi n q i) := by
  unfold psi
  exact (((continuous_entry 0 0).pow i).mul ((continuous_entry 1 0).pow (n - i))).mul
    (continuous_det.zpow₀ q fun k => Or.inl (det_ne_zero_of_U2 k))

theorem coe_inv_U2 (k : U2) : ((k⁻¹ : U2) : Matrix (Fin 2) (Fin 2) ℂ) = star (k : Matrix (Fin 2) (Fin 2) ℂ) :=
  rfl

theorem det_star_U2 (k : U2) :
    (star (k : Matrix (Fin 2) (Fin 2) ℂ)).det = conj ((k : Matrix (Fin 2) (Fin 2) ℂ).det) := by
  rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]; rfl

theorem psi_inv_mul (n : ℕ) (q : ℤ) (k l : U2) :
    psi n q n (k⁻¹ * l) = ∑ i ∈ range (n + 1), (n.choose i : ℂ) * conj (psi n q i k) * psi n q i l := by
  have h00 : ((k⁻¹ * l : U2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 =
      conj ((k : Matrix (Fin 2) (Fin 2) ℂ) 0 0) * (l : Matrix (Fin 2) (Fin 2) ℂ) 0 0 +
        conj ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0) * (l : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by
    rw [Matrix.UnitaryGroup.mul_val, coe_inv_U2, Matrix.mul_apply, Fin.sum_univ_two]
    simp [Matrix.star_apply]
  have hdet : ((k⁻¹ * l : U2) : Matrix (Fin 2) (Fin 2) ℂ).det =
      conj ((k : Matrix (Fin 2) (Fin 2) ℂ).det) * (l : Matrix (Fin 2) (Fin 2) ℂ).det := by
    rw [Matrix.UnitaryGroup.mul_val, coe_inv_U2, Matrix.det_mul, det_star_U2]
  simp only [psi, Nat.sub_self, pow_zero, mul_one]
  rw [h00, hdet, add_pow, mul_zpow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mul_pow, mul_pow]
  simp only [map_mul, map_pow, map_zpow₀]
  ring

theorem psi_self_inv (n : ℕ) (q : ℤ) (k : U2) : psi n q n k⁻¹ = conj (psi n q n k) := by
  simp only [psi, Nat.sub_self, pow_zero, mul_one, coe_inv_U2, det_star_U2, map_mul, map_pow,
    map_zpow₀]
  simp [Matrix.star_apply]

theorem psi_one (n : ℕ) (q : ℤ) : psi n q n 1 = 1 := by
  simp [psi]

theorem psi_tC_mul (n : ℕ) (q : ℤ) {i : ℕ} (hi : i ≤ n) (a b : ℝ) (k : U2) :
    psi n q i (tC a b * k) =
      Complex.exp (I * ((((i : ℝ) + q) * a + ((n : ℝ) - i + q) * b : ℝ) : ℂ)) * psi n q i k := by
  have h00 : ((tC a b * k : U2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 =
      Complex.exp (a * I) * (k : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
    rw [Matrix.UnitaryGroup.mul_val, coe_tC, Matrix.mul_apply, Fin.sum_univ_two]; simp
  have h10 : ((tC a b * k : U2) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 =
      Complex.exp (b * I) * (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by
    rw [Matrix.UnitaryGroup.mul_val, coe_tC, Matrix.mul_apply, Fin.sum_univ_two]; simp
  have hdet : ((tC a b * k : U2) : Matrix (Fin 2) (Fin 2) ℂ).det =
      (Complex.exp (a * I) * Complex.exp (b * I)) * (k : Matrix (Fin 2) (Fin 2) ℂ).det := by
    rw [Matrix.UnitaryGroup.mul_val, Matrix.det_mul, coe_tC, Matrix.det_fin_two_of]; ring
  simp only [psi, h00, h10, hdet]
  rw [mul_pow, mul_pow, mul_zpow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_add, ← Complex.exp_int_mul]
  have hc : (((n - i : ℕ) : ℂ)) = (n : ℂ) - i := by push_cast [Nat.cast_sub hi]; ring
  have e : Complex.exp (I * ((((i : ℝ) + q) * a + ((n : ℝ) - i + q) * b : ℝ) : ℂ)) =
      Complex.exp (↑i * (↑a * I)) * Complex.exp (↑(n - i) * (↑b * I)) *
        Complex.exp (↑q * (↑a * I + ↑b * I)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, hc]; congr 1; push_cast; ring
  rw [e]; ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : UnitaryRep GL2C H)

theorem continuous_orbit_K (x : H) : Continuous fun k : U2 => σ (kC k) x :=
  (σ.continuous_orbit x).comp continuous_kC

theorem integrable_of_continuous {E : Type*} [NormedAddCommGroup E] {f : U2 → E}
    (hf : Continuous f) : Integrable f μK :=
  hf.integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))

noncomputable def Kint (φ : U2 → ℂ) (x : H) : H := ∫ k, φ k • σ (kC k) x ∂μK

theorem integrable_Kint {φ : U2 → ℂ} (hφ : Continuous φ) (x : H) :
    Integrable (fun k => φ k • σ (kC k) x) μK :=
  integrable_of_continuous (hφ.smul (continuous_orbit_K σ x))

theorem Kint_add {φ : U2 → ℂ} (hφ : Continuous φ) (x y : H) :
    Kint σ φ (x + y) = Kint σ φ x + Kint σ φ y := by
  unfold Kint
  rw [← integral_add (integrable_Kint σ hφ x) (integrable_Kint σ hφ y)]
  congr 1; funext k; rw [map_add, smul_add]

theorem Kint_smul (φ : U2 → ℂ) (c : ℂ) (x : H) : Kint σ φ (c • x) = c • Kint σ φ x := by
  unfold Kint
  rw [← integral_smul]
  congr 1; funext k; rw [map_smul, smul_comm]

theorem map_Kint {φ : U2 → ℂ} (hφ : Continuous φ) (g : GL2C) (x : H) :
    σ g (Kint σ φ x) = ∫ k, φ k • σ (g * kC k) x ∂μK := by
  unfold Kint
  rw [← ContinuousLinearMap.integral_comp_comm (σ g : H →L[ℂ] H) (integrable_Kint σ hφ x)]
  congr 1; funext k
  simp [UnitaryRep.map_mul_apply]

theorem map_kC_Kint {φ : U2 → ℂ} (hφ : Continuous φ) (l : U2) (x : H) :
    σ (kC l) (Kint σ φ x) = Kint σ (fun k => φ (l⁻¹ * k)) x := by
  rw [map_Kint σ hφ, Kint]
  conv_rhs => rw [← integral_mul_left_K (fun k => φ (l⁻¹ * k) • σ (kC k) x) l]
  congr 1; funext k
  simp [map_mul, inv_mul_cancel_left]

theorem inner_Kint_right {φ : U2 → ℂ} (hφ : Continuous φ) (x y : H) :
    ⟪y, Kint σ φ x⟫_ℂ = ∫ k, φ k * ⟪y, σ (kC k) x⟫_ℂ ∂μK := by
  unfold Kint
  rw [← integral_inner (integrable_Kint σ hφ x)]
  congr 1; funext k; rw [inner_smul_right]

noncomputable def Q (n : ℕ) (q : ℤ) (i : ℕ) (x : H) : H := Kint σ (fun k => conj (psi n q i k)) x

theorem continuous_conj_psi (n : ℕ) (q : ℤ) (i : ℕ) : Continuous fun k => conj (psi n q i k) :=
  continuous_conj.comp (continuous_psi n q i)

theorem map_Q (n : ℕ) (q : ℤ) (l : U2) (x : H) :
    σ (kC l) (Q σ n q n x) =
      ∑ i ∈ range (n + 1), ((n.choose i : ℂ) * psi n q i l) • Q σ n q i x := by
  rw [Q, map_kC_Kint σ (continuous_conj_psi n q n)]
  simp only [Q, Kint]
  simp_rw [← integral_smul]
  rw [← integral_finset_sum]
  · congr 1; funext k
    rw [psi_inv_mul, map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
    congr 1
    simp only [map_mul, map_natCast, starRingEnd_self_apply]
  · intro i _
    exact (integrable_Kint σ (continuous_conj_psi n q i) x).smul _

theorem map_tC_Q (n : ℕ) (q : ℤ) {i : ℕ} (hi : i ≤ n) (a b : ℝ) (x : H) :
    σ (kC (tC a b)) (Q σ n q i x) =
      Complex.exp (I * ((((i : ℝ) + q) * a + ((n : ℝ) - i + q) * b : ℝ) : ℂ)) • Q σ n q i x := by
  simp only [Q]
  rw [map_kC_Kint σ (continuous_conj_psi n q i), Kint, Kint, ← integral_smul]
  congr 1; funext k
  have hinv : (tC a b)⁻¹ = tC (-a) (-b) := by
    rw [inv_eq_iff_mul_eq_one]
    apply Subtype.ext
    rw [Matrix.UnitaryGroup.mul_val, coe_tC, coe_tC]
    ext r s; fin_cases r <;> fin_cases s <;> simp [← Complex.exp_add]
  rw [hinv, psi_tC_mul n q hi, smul_smul, map_mul, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, conj_I, map_add, map_sub, map_neg, Complex.conj_ofReal, map_intCast,
    map_natCast]
  push_cast
  ring

theorem conj_exp_mul_exp (r s : ℝ) :
    conj (Complex.exp (I * r)) * Complex.exp (I * s) = Complex.exp (I * ((s - r : ℝ) : ℂ)) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem integral_conj_psi_mul_psi (n : ℕ) (q : ℤ) {i : ℕ} (hi : i ≤ n) (hin : i ≠ n) :
    ∫ k, conj (psi n q n k) * psi n q i k ∂μK = 0 := by
  set J := ∫ k, conj (psi n q n k) * psi n q i k ∂μK with hJ
  have hlt : (i : ℝ) < n := by exact_mod_cast lt_of_le_of_ne hi hin
  set a : ℝ := Real.pi / ((n : ℝ) - i) with ha
  have hexp : Complex.exp (I * ((((i : ℝ) + q) * a + ((n : ℝ) - i + q) * 0 -
      (((n : ℝ) + q) * a + ((n : ℝ) - n + q) * 0) : ℝ) : ℂ)) = -1 := by
    have : ((i : ℝ) + q) * a + ((n : ℝ) - i + q) * 0 - (((n : ℝ) + q) * a + ((n : ℝ) - n + q) * 0) =
        -Real.pi := by
      have hne : (n : ℝ) - i ≠ 0 := by linarith
      rw [ha]; field_simp; ring
    rw [this]; push_cast
    rw [mul_neg, Complex.exp_neg, mul_comm, Complex.exp_pi_mul_I]; norm_num
  have key : J = -J := by
    conv_lhs => rw [hJ, ← integral_mul_left_K _ (tC a 0)]
    rw [hJ, ← integral_neg]
    congr 1; funext k
    rw [psi_tC_mul n q hi, psi_tC_mul n q le_rfl, map_mul,
      show ∀ e₁ p e₂ r : ℂ, conj e₁ * p * (e₂ * r) = (conj e₁ * e₂) * (p * r) by intros; ring,
      conj_exp_mul_exp, hexp]
    ring
  have : (2 : ℂ) * J = 0 := by linear_combination key
  simpa using this

noncomputable def normSqInt (n : ℕ) (q : ℤ) : ℝ := ∫ k, ‖psi n q n k‖ ^ 2 ∂μK

theorem normSqInt_pos (n : ℕ) (q : ℤ) : 0 < normSqInt n q := by
  have hc : Continuous fun k => ‖psi n q n k‖ ^ 2 := (continuous_psi n q n).norm.pow 2
  rw [normSqInt, integral_pos_iff_support_of_nonneg (fun k => by positivity)
    (integrable_of_continuous hc)]
  exact (isOpen_ne_fun hc continuous_const).measure_pos μK ⟨1, by simp [psi_one]⟩

theorem integral_conj_psi_self (n : ℕ) (q : ℤ) :
    ∫ k, conj (psi n q n k) * psi n q n k ∂μK = (normSqInt n q : ℂ) := by
  rw [normSqInt, ← integral_complex_ofReal]
  congr 1; funext k
  rw [Complex.conj_mul']; push_cast; ring

theorem collapse (n : ℕ) (q : ℤ) (u : ℕ → H) :
    ((normSqInt n q)⁻¹ : ℂ) • ∫ k, conj (psi n q n k) •
      ∑ i ∈ range (n + 1), ((n.choose i : ℂ) * psi n q i k) • u i ∂μK = u n := by
  have hint : ∀ i, Integrable (fun k => (conj (psi n q n k) * ((n.choose i : ℂ) * psi n q i k))) μK :=
    fun i => integrable_of_continuous ((continuous_conj_psi n q n).mul
      (continuous_const.mul (continuous_psi n q i)))
  have e : (fun k => conj (psi n q n k) • ∑ i ∈ range (n + 1), ((n.choose i : ℂ) * psi n q i k) • u i) =
      fun k => ∑ i ∈ range (n + 1), (conj (psi n q n k) * ((n.choose i : ℂ) * psi n q i k)) • u i := by
    funext k; rw [Finset.smul_sum]; simp_rw [smul_smul]
  rw [e, integral_finset_sum _ (fun i _ => (hint i).smul_const _)]
  simp_rw [integral_smul_const]
  rw [Finset.sum_eq_single n]
  · have h1 : ∫ k, conj (psi n q n k) * ((n.choose n : ℂ) * psi n q n k) ∂μK = (normSqInt n q : ℂ) := by
      simp only [Nat.choose_self, Nat.cast_one, one_mul]; exact integral_conj_psi_self n q
    rw [h1, smul_smul, inv_mul_cancel₀ (by exact_mod_cast (normSqInt_pos n q).ne'), one_smul]
  · intro i hi hin
    have : ∫ k, conj (psi n q n k) * ((n.choose i : ℂ) * psi n q i k) ∂μK = 0 := by
      simp_rw [show ∀ k, conj (psi n q n k) * ((n.choose i : ℂ) * psi n q i k) =
        (n.choose i : ℂ) * (conj (psi n q n k) * psi n q i k) from fun k => by ring]
      rw [integral_const_mul, integral_conj_psi_mul_psi n q (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hin,
        mul_zero]
    rw [this, zero_smul]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h

noncomputable def P (n : ℕ) (q : ℤ) (x : H) : H := ((normSqInt n q)⁻¹ : ℂ) • Q σ n q n x

theorem map_P (n : ℕ) (q : ℤ) (l : U2) (x : H) :
    σ (kC l) (P σ n q x) = ∑ i ∈ range (n + 1),
      ((n.choose i : ℂ) * psi n q i l) • (((normSqInt n q)⁻¹ : ℂ) • Q σ n q i x) := by
  rw [P, map_smul, map_Q, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm]

theorem P_P (n : ℕ) (q : ℤ) (x : H) : P σ n q (P σ n q x) = P σ n q x := by
  conv_lhs => rw [P, Q, Kint]
  simp_rw [map_P]
  rw [collapse n q (fun i => ((normSqInt n q)⁻¹ : ℂ) • Q σ n q i x)]
  rfl

theorem inner_Q_left (n : ℕ) (q : ℤ) (x y : H) : ⟪Q σ n q n x, y⟫_ℂ = ⟪x, Q σ n q n y⟫_ℂ := by
  rw [← inner_conj_symm, Q, inner_Kint_right σ (continuous_conj_psi n q n), Q,
    inner_Kint_right σ (continuous_conj_psi n q n), ← integral_conj]
  set F : U2 → ℂ := fun k => conj (psi n q n k) * ⟪x, σ (kC k) y⟫_ℂ with hF
  rw [← integral_inv_K F]
  congr 1; funext k
  simp only [hF, map_mul, starRingEnd_self_apply, inner_conj_symm, psi_self_inv, map_inv]
  rw [UnitaryRep.inner_map_left]

theorem P_add (n : ℕ) (q : ℤ) (x y : H) : P σ n q (x + y) = P σ n q x + P σ n q y := by
  simp only [P, Q, Kint_add σ (continuous_conj_psi n q n), smul_add]

theorem P_smul (n : ℕ) (q : ℤ) (c : ℂ) (x : H) : P σ n q (c • x) = c • P σ n q x := by
  simp only [P, Q, Kint_smul, smul_comm c]

theorem inner_P_left (n : ℕ) (q : ℤ) (x y : H) : ⟪P σ n q x, y⟫_ℂ = ⟪x, P σ n q y⟫_ℂ := by
  rw [P, P, inner_smul_left, inner_smul_right, inner_Q_left]
  congr 1
  rw [← Complex.ofReal_inv, Complex.conj_ofReal]

theorem norm_P_le (n : ℕ) (q : ℤ) (x : H) : ‖P σ n q x‖ ≤ ‖x‖ := by
  have h : ‖P σ n q x‖ ^ 2 ≤ ‖x‖ * ‖P σ n q x‖ := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_P_left, P_P]
    exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  by_cases h0 : ‖P σ n q x‖ = 0
  · rw [h0]; exact norm_nonneg _
  · nlinarith [norm_nonneg (P σ n q x), lt_of_le_of_ne (norm_nonneg (P σ n q x)) (Ne.symm h0)]

noncomputable def PL (n : ℕ) (q : ℤ) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := P σ n q
      map_add' := P_add σ n q
      map_smul' := P_smul σ n q } 1 (fun x => by simpa using norm_P_le σ n q x)

@[simp] theorem PL_apply (n : ℕ) (q : ℤ) (x : H) : PL σ n q x = P σ n q x := rfl

def W (n : ℕ) (q : ℤ) : Submodule ℂ H where
  carrier := {x | P σ n q x = x}
  add_mem' {x y} hx hy := by
    show P σ n q (x + y) = x + y
    rw [P_add, show P σ n q x = x from hx, show P σ n q y = y from hy]
  zero_mem' := by simpa using P_smul σ n q 0 0
  smul_mem' c x hx := by
    show P σ n q (c • x) = c • x
    rw [P_smul, show P σ n q x = x from hx]

theorem mem_W {n : ℕ} {q : ℤ} {x : H} : x ∈ W σ n q ↔ P σ n q x = x := Iff.rfl

theorem isClosed_divisorComponent (n : ℕ) (q : ℤ) : IsClosed (W σ n q : Set H) :=
  isClosed_eq (PL σ n q).continuous continuous_id

theorem P_mem_alt (n : ℕ) (q : ℤ) (x : H) : P σ n q x ∈ W σ n q := P_P σ n q x

theorem inner_P_of_mem {n : ℕ} {q : ℤ} {y : H} (hy : y ∈ W σ n q) (u : H) :
    ⟪y, P σ n q u⟫_ℂ = ⟪y, u⟫_ℂ := by
  rw [← inner_P_left, hy]

end KT

end GroundTheory.Automorphic.ArchWhittakerC
