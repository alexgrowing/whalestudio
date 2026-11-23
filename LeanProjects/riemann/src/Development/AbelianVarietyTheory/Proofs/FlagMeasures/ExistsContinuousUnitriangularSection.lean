import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.UnitriSection

open Matrix

section Alg

variable {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J : Matrix (Fin n) (Fin n) A)

theorem hf_add_l (x y z : Fin n → A) :
    Formalism.UG.hform s J (x + y) z = Formalism.UG.hform s J x z + Formalism.UG.hform s J y z := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hf_smul_l (c : A) (x z : Fin n → A) :
    Formalism.UG.hform s J (c • x) z = s c * Formalism.UG.hform s J x z := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem hf_add_r (x y z : Fin n → A) :
    Formalism.UG.hform s J x (y + z) = Formalism.UG.hform s J x y + Formalism.UG.hform s J x z := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hf_smul_r (c : A) (x z : Fin n → A) :
    Formalism.UG.hform s J x (c • z) = c * Formalism.UG.hform s J x z := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_sum_l {ι : Type} (t : Finset ι) (c : ι → A) (x : ι → Fin n → A) (z : Fin n → A) :
    Formalism.UG.hform s J (∑ i ∈ t, c i • x i) z = ∑ i ∈ t, s (c i) * Formalism.UG.hform s J (x i) z := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [Formalism.UG.hform]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf_add_l, hf_smul_l, ih]

theorem hf_symm (hs : ∀ a, s (s a) = a) (hJ : ∀ i j, s (J j i) = J i j) (x y : Fin n → A) :
    s (Formalism.UG.hform s J x y) = Formalism.UG.hform s J y x := by
  simp only [Formalism.UG.hform, map_sum, map_mul, hs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

def row (u : Fin n → A) : Fin n → A := Matrix.vecMul (s ∘ u) J

theorem row_dot (u x : Fin n → A) : row s J u ⬝ᵥ x = Formalism.UG.hform s J u x := by
  rw [row, ← Matrix.dotProduct_mulVec, Formalism.UG.P.hform_eq_dot]

def eich (u w : Fin n → A) (c : A) : Matrix (Fin n) (Fin n) A :=
  1 + Matrix.vecMulVec w (row s J u) + Matrix.vecMulVec u (c • row s J u - row s J w)

theorem eich_mulVec (u w : Fin n → A) (c : A) (x : Fin n → A) :
    eich s J u w c *ᵥ x = x + Formalism.UG.hform s J u x • w
      + (c * Formalism.UG.hform s J u x - Formalism.UG.hform s J w x) • u := by
  simp only [eich, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, sub_dotProduct,
    smul_dotProduct, row_dot, smul_eq_mul, op_smul_eq_smul]

theorem eich_unitary (hs : ∀ a, s (s a) = a) (hJ : ∀ i j, s (J j i) = J i j) (u w : Fin n → A)
    (c : A) (huu : Formalism.UG.hform s J u u = 0) (huw : Formalism.UG.hform s J u w = 0)
    (hc : c + s c + Formalism.UG.hform s J w w = 0) :
    Formalism.UG.cT s (eich s J u w c) * J * eich s J u w c = J := by
  have hwu : Formalism.UG.hform s J w u = 0 := by rw [← hf_symm s J hs hJ, huw, map_zero]
  have key : ∀ x y, Formalism.UG.hform s J (eich s J u w c *ᵥ x) (eich s J u w c *ᵥ y)
      = Formalism.UG.hform s J x y := by
    intro x y
    have hxu : Formalism.UG.hform s J x u = s (Formalism.UG.hform s J u x) := (hf_symm s J hs hJ u x).symm
    have hxw : Formalism.UG.hform s J x w = s (Formalism.UG.hform s J w x) := (hf_symm s J hs hJ w x).symm
    rw [eich_mulVec, eich_mulVec]
    simp only [hf_add_l, hf_add_r, hf_smul_l, hf_smul_r, map_sub, map_mul, huu, huw, hwu, hxu, hxw]
    linear_combination (s (Formalism.UG.hform s J u x) * Formalism.UG.hform s J u y) * hc
  ext i j
  have := key (Pi.single i 1) (Pi.single j 1)
  rw [Formalism.UG.P.hform_mulVec, Formalism.UG.P.hform_single, Formalism.UG.P.hform_single] at this
  exact this

end Alg

section Frame

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem sigR_inclR (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem sigR_invol (hσ : ∀ e, σ (σ e) = e) (a : R ⊗[F] E) : sigR R σ (sigR R σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem JR_herm (hJ : IsHermND σ J) (i j : Fin n) : sigR R σ (JR R J j i) = JR R J i j := by
  simp only [JR, Matrix.map_apply, sigR_inclR, hJ.1 i j]

theorem h_rat (x y : Fin n → E) :
    Formalism.UG.hform (sigR R σ) (JR R J) (ratV (F := F) R x) (ratV (F := F) R y) = inclR R (hE σ J x y) := by
  simp [Formalism.UG.hform, hE, ratV, JR, map_sum, map_mul, sigR_inclR]

variable {r : ℕ}

def coef (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → R ⊗[F] E) (b a : Fin (r + 1)) :
    R ⊗[F] E := if h : a < b then x ⟨(a, b), h⟩ else 0

theorem coef_last (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → R ⊗[F] E) (b : Fin (r + 1)) :
    coef R x b (Fin.last r) = 0 := by
  simp [coef, not_lt.2 (Fin.le_last b)]

def yv (P : Frame E n r) (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → R ⊗[F] E)
    (b : Fin (r + 1)) : Fin n → R ⊗[F] E :=
  ∑ a, coef R x b a • ratV (F := F) R (F0 P a)

def wv (P : Frame E n r) (T : F) (b : Fin (r + 1)) : Fin n → R ⊗[F] E :=
  Fin.lastCases (inclR (F := F) R (algebraMap F E T⁻¹) • ratV (F := F) R P.z)
    (fun i => (-1 : R ⊗[F] E) • ratV (F := F) R (P.f i)) b

def cc (T : F) (b : Fin (r + 1)) : R ⊗[F] E :=
  Fin.lastCases (inclR (F := F) R (algebraMap F E (2 * T)⁻¹)) (fun _ => 0) b

end Frame

section Facts

variable {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (P : Frame E n r) (T : F)

variable {R σ J P T}

theorem frameInitialVectors_castSucc (i : Fin r) : F0 P (Fin.castSucc i) = P.e i := by simp [F0]
theorem frameInitialVectors_last : F0 P (Fin.last r) = P.z := by simp [F0]

theorem hE_symm (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J) (x y : Fin n → E) :
    σ (hE σ J x y) = hE σ J y x :=
  hf_symm (σ : E →+* E) J hσ hJ.1 x y

theorem hermitianFormE_frameE_initialVectors (hP : P.IsStd σ J T) (i : Fin r) (c : Fin (r + 1)) : hE σ J (P.e i) (F0 P c) = 0 := by
  induction c using Fin.lastCases with
  | last => rw [frameInitialVectors_last]; exact hP.2.2.2.1 i
  | cast k => rw [frameInitialVectors_castSucc]; exact hP.1 i k

theorem hermitianFormE_frameZ_initialVectors (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (c : Fin (r + 1)) :
    hE σ J P.z (F0 P c) = if c = Fin.last r then algebraMap F E (-T) else 0 := by
  induction c using Fin.lastCases with
  | last => rw [frameInitialVectors_last, if_pos rfl]; exact hP.2.2.2.2.2.1
  | cast k =>
    rw [frameInitialVectors_castSucc, if_neg (Fin.castSucc_ne_last k), ← hE_symm hσ hJ, hP.2.2.2.1 k, map_zero]

theorem hermitian_flag_dual_basis (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (j : Fin r)
    (c : Fin (r + 1)) : hE σ J (P.f j) (F0 P c) = if c = Fin.castSucc j then 1 else 0 := by
  induction c using Fin.lastCases with
  | last => rw [frameInitialVectors_last, if_neg (Fin.castSucc_ne_last j).symm]; exact hP.2.2.2.2.1 j
  | cast k =>
    rw [frameInitialVectors_castSucc, ← hE_symm hσ hJ, hP.2.2.1 k j]
    by_cases h : k = j
    · subst h; simp
    · simp [h, Fin.castSucc_inj]

local notation "hA" => Formalism.UG.hform (sigR R σ) (JR R J)

variable (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → R ⊗[F] E)

theorem yv_perp (hP : P.IsStd σ J T) (b c : Fin (r + 1)) :
    hA (yv R P x b) (ratV (F := F) R (F0 P c)) = 0 := by
  unfold yv
  rw [hf_sum_l]
  refine Finset.sum_eq_zero fun a _ => ?_
  induction a using Fin.lastCases with
  | last => rw [coef_last, map_zero, zero_mul]
  | cast i => rw [frameInitialVectors_castSucc, h_rat, hermitianFormE_frameE_initialVectors hP, map_zero, mul_zero]

theorem yv_iso (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (b : Fin (r + 1)) :
    hA (yv R P x b) (yv R P x b) = 0 := by
  have h1 := hf_sum_l (sigR R σ) (JR R J) Finset.univ (coef R x b)
    (fun a => ratV (F := F) R (F0 P a)) (yv R P x b)
  rw [show hA (yv R P x b) (yv R P x b) = hA (∑ a, coef R x b a • ratV (F := F) R (F0 P a)) (yv R P x b)
    from rfl, h1]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [← hf_symm _ _ (sigR_invol R σ hσ) (fun i j => JR_herm R σ J hJ i j), yv_perp x hP, map_zero, mul_zero]

theorem yv_w (hP : P.IsStd σ J T) (b : Fin (r + 1)) : hA (yv R P x b) (wv R P T b) = 0 := by
  induction b using Fin.lastCases with
  | last =>
    simp only [wv, Fin.lastCases_last]
    rw [hf_smul_r, ← frameInitialVectors_last (P := P), yv_perp x hP, mul_zero]
  | cast j =>
    simp only [wv, Fin.lastCases_castSucc]
    rw [hf_smul_r]
    unfold yv
    rw [hf_sum_l, Finset.sum_eq_zero, mul_zero]
    intro a _
    induction a using Fin.lastCases with
    | last => rw [coef_last, map_zero, zero_mul]
    | cast i =>
      by_cases hij : Fin.castSucc i < Fin.castSucc j
      · rw [frameInitialVectors_castSucc, h_rat, hP.2.2.1 i j, if_neg (ne_of_lt (Fin.castSucc_lt_castSucc_iff.1 hij)),
          map_zero, mul_zero]
      · simp [coef, hij]

theorem cc_cond (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (b : Fin (r + 1)) :
    cc R T b + sigR R σ (cc R T b) + hA (wv R P T b) (wv R P T b) = 0 := by
  induction b using Fin.lastCases with
  | last =>
    simp only [wv, cc, Fin.lastCases_last]
    rw [hf_smul_l, hf_smul_r, h_rat, hP.2.2.2.2.2.1]
    simp only [sigR_inclR, AlgHom.commutes]
    have hT := hP.2.2.2.2.2.2
    have h0 : (2 * T)⁻¹ + (2 * T)⁻¹ + T⁻¹ * (T⁻¹ * -T) = 0 := by
      field_simp
      ring
    have h1 := congrArg (fun t => inclR (F := F) R (algebraMap F E t)) h0
    simp only [map_add, map_mul, map_neg, map_zero] at h1 ⊢
    linear_combination h1
  | cast j =>
    simp only [wv, cc, Fin.lastCases_castSucc]
    rw [hf_smul_l, hf_smul_r, h_rat, hP.2.1 j j]
    simp

theorem unitriangularEichlerSecondVector_initialVectors (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (b c : Fin (r + 1)) :
    hA (wv R P T b) (ratV (F := F) R (F0 P c)) = -(if c = b then 1 else 0) := by
  induction b using Fin.lastCases with
  | last =>
    simp only [wv, Fin.lastCases_last]
    rw [hf_smul_l, h_rat, hermitianFormE_frameZ_initialVectors hσ hJ hP, sigR_inclR, AlgHom.commutes]
    by_cases hc : c = Fin.last r
    · rw [if_pos hc, if_pos hc, ← map_mul, ← map_mul, mul_neg, inv_mul_cancel₀ hP.2.2.2.2.2.2]
      simp
    · rw [if_neg hc, if_neg hc]; simp
  | cast j =>
    simp only [wv, Fin.lastCases_castSucc]
    rw [hf_smul_l, h_rat, hermitian_flag_dual_basis hσ hJ hP]
    by_cases hc : c = Fin.castSucc j
    · rw [if_pos hc, if_pos hc]; simp
    · rw [if_neg hc, if_neg hc]; simp

end Facts

section Product

variable {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (P : Frame E n r) (T : F)

def Mb (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → R ⊗[F] E) (b : Fin (r + 1)) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  eich (sigR R σ) (JR R J) (yv R P x b) (wv R P T b) (cc R T b)

def Pm (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → R ⊗[F] E) (k : ℕ) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  Nat.rec (motive := fun _ => Matrix (Fin n) (Fin n) (R ⊗[F] E)) 1
    (fun k M => (if h : k < r + 1 then Mb R σ J P T x ⟨k, h⟩ else 1) * M) k

theorem Pm_zero (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → R ⊗[F] E) :
    Pm R σ J P T x 0 = 1 := rfl

theorem Pm_succ (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → R ⊗[F] E) (k : ℕ) :
    Pm R σ J P T x (k + 1) = (if h : k < r + 1 then Mb R σ J P T x ⟨k, h⟩ else 1) * Pm R σ J P T x k := rfl

variable {R σ J P T}
variable (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → R ⊗[F] E)

theorem unitriangularColumnEichlerMatrix_initialVectors (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (b c : Fin (r + 1)) :
    Mb R σ J P T x b *ᵥ ratV (F := F) R (F0 P c) =
      ratV (F := F) R (F0 P c) + (if c = b then yv R P x b else 0) := by
  rw [Mb, eich_mulVec, yv_perp x hP, unitriangularEichlerSecondVector_initialVectors hσ hJ hP]
  by_cases h : c = b
  · simp [h]
  · simp [h]

theorem Mb_fix (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (k c : Fin (r + 1))
    (hck : c ≤ k) : Mb R σ J P T x k *ᵥ yv R P x c = yv R P x c := by
  show Mb R σ J P T x k *ᵥ (∑ a, coef R x c a • ratV (F := F) R (F0 P a)) =
    ∑ a, coef R x c a • ratV (F := F) R (F0 P a)
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mulVec_smul, unitriangularColumnEichlerMatrix_initialVectors x hσ hJ hP]
  by_cases ha : a = k
  · subst ha
    have : coef R x c a = 0 := by simp [coef, not_lt.2 hck]
    simp [this]
  · simp [ha]

theorem unitriangularEichlerPartialProduct_initialVectors (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (k : ℕ) (c : Fin (r + 1)) :
    Pm R σ J P T x k *ᵥ ratV (F := F) R (F0 P c) =
      ratV (F := F) R (F0 P c) + (if c.val < k then yv R P x c else 0) := by
  induction k with
  | zero => simp [Pm_zero]
  | succ k ih =>
    rw [Pm_succ, ← Matrix.mulVec_mulVec, ih]
    by_cases hk : k < r + 1
    · rw [dif_pos hk, Matrix.mulVec_add, unitriangularColumnEichlerMatrix_initialVectors x hσ hJ hP]
      by_cases hck : c.val < k
      · have hne : c ≠ ⟨k, hk⟩ := fun h => by rw [h] at hck; exact lt_irrefl _ hck
        rw [if_pos hck, Mb_fix x hσ hJ hP _ _ (by rw [Fin.le_iff_val_le_val]; simp only [Fin.val_mk]; omega),
          if_pos (by omega : c.val < k + 1), if_neg hne, add_zero]
      · rw [if_neg hck, Matrix.mulVec_zero, add_zero]
        by_cases hce : c.val = k
        · have hc : c = ⟨k, hk⟩ := Fin.ext hce
          rw [if_pos hc, if_pos (by omega : c.val < k + 1), hc]
        · have hne : c ≠ ⟨k, hk⟩ := fun h => hce (by rw [h])
          rw [if_neg hne, if_neg (by omega : ¬ c.val < k + 1)]
    · have := c.isLt
      rw [dif_neg hk, Matrix.one_mulVec, if_pos (by omega : c.val < k), if_pos (by omega : c.val < k + 1)]

theorem Pm_unitary (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (k : ℕ) :
    Formalism.UG.cT (sigR R σ) (Pm R σ J P T x k) * JR R J * Pm R σ J P T x k = JR R J := by
  induction k with
  | zero => simp [Pm_zero, Formalism.UG.cT_one]
  | succ k ih =>
    rw [Pm_succ]
    set M : Matrix (Fin n) (Fin n) (R ⊗[F] E) := if h : k < r + 1 then Mb R σ J P T x ⟨k, h⟩ else 1
    have hM : Formalism.UG.cT (sigR R σ) M * JR R J * M = JR R J := by
      simp only [M]
      split_ifs with hk
      · exact eich_unitary _ _ (sigR_invol R σ hσ) (fun i j => JR_herm R σ J hJ i j) _ _ _
          (yv_iso x hσ hJ hP _) (yv_w x hP _) (cc_cond hσ hJ hP _)
      · simp [Formalism.UG.cT_one]
    rw [Formalism.UG.cT_mul]
    calc Formalism.UG.cT (sigR R σ) (Pm R σ J P T x k) * Formalism.UG.cT (sigR R σ) M * JR R J * (M * Pm R σ J P T x k)
        = Formalism.UG.cT (sigR R σ) (Pm R σ J P T x k) * (Formalism.UG.cT (sigR R σ) M * JR R J * M) *
            Pm R σ J P T x k := by simp only [Matrix.mul_assoc]
      _ = JR R J := by rw [hM, ih]

end Product

section Units

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem JR_det_isUnit (hJ : IsHermND σ J) : IsUnit (JR (F := F) R J).det := by
  have h : (JR (F := F) R J).det = inclR (F := F) R J.det := by
    rw [JR, RingHom.map_det]
    rfl
  rw [h]
  exact (isUnit_iff_ne_zero.2 hJ.2).map _

variable {R σ J}

theorem inv_mul_of_unitary (hdet : IsUnit (JR (F := F) R J).det) (M : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (hM : Formalism.UG.cT (sigR R σ) M * JR (F := F) R J * M = JR (F := F) R J) :
    (JR (F := F) R J)⁻¹ * Formalism.UG.cT (sigR R σ) M * JR (F := F) R J * M = 1 := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Formalism.UG.cT (sigR R σ) M), hM,
    Matrix.nonsing_inv_mul _ hdet]

def uOf (hdet : IsUnit (JR (F := F) R J).det) (M : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (hM : Formalism.UG.cT (sigR R σ) M * JR (F := F) R J * M = JR (F := F) R J) : GL (Fin n) (R ⊗[F] E) where
  val := M
  inv := (JR (F := F) R J)⁻¹ * Formalism.UG.cT (sigR R σ) M * JR (F := F) R J
  val_inv := mul_eq_one_comm.1 (inv_mul_of_unitary hdet M hM)
  inv_val := inv_mul_of_unitary hdet M hM

def mkHA (hdet : IsUnit (JR (F := F) R J).det) (M : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (hM : Formalism.UG.cT (sigR R σ) M * JR (F := F) R J * M = JR (F := F) R J) : HA R σ J :=
  (⟨uOf hdet M hM, hM⟩ : HR R σ J)

theorem lin_mkHA (hdet : IsUnit (JR (F := F) R J).det) (M : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (hM : Formalism.UG.cT (sigR R σ) M * JR (F := F) R J * M = JR (F := F) R J) (w : Fin n → R ⊗[F] E) :
    lin R σ J (mkHA hdet M hM) w = M *ᵥ w := rfl

end Units

theorem unitri_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∃ t : ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E) → HA (Fv F v) σ J, Continuous t ∧ (∀ x b, lin (Fv F v) σ J (t x) (ratV (F := F) (Fv F v) (F0 P b)) = ∑ a : Fin (r + 1), (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : Fv F v ⊗[F] E) • ratV (F := F) (Fv F v) (F0 P a)) := by
  intro F E _ _ _ _ _ σ hCM n J hJ v r P T hP
  have hσ : ∀ e, σ (σ e) = e := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    intro e
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hr : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  have hs : Continuous (sigR (Fv F v) σ) := by
    let L := LinearMap.baseChange (Fv F v) (σ.toLinearMap)
    have hL : ∀ a, sigR (Fv F v) σ a = L a := by
      intro a
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [sigR, L]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    have hc : Continuous L := IsModuleTopology.continuous_of_linearMap L
    exact hc.congr fun a => (hL a).symm
  have hdet := JR_det_isUnit (Fv F v) σ J hJ
  have hy : ∀ b, Continuous fun x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E =>
      yv (Fv F v) P x b := by
    intro b
    refine continuous_finset_sum _ fun a _ => ?_
    have hc : Continuous fun x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E =>
        coef (Fv F v) x b a := by
      by_cases h : a < b
      · simp only [coef, dif_pos h]
        exact continuous_apply _
      · simp only [coef, dif_neg h]
        exact continuous_const
    exact hc.smul continuous_const
  have hMb : ∀ b, Continuous fun x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E =>
      Mb (Fv F v) σ J P T x b := by
    intro b
    have hsy : Continuous fun x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E =>
        (sigR (Fv F v) σ ∘ yv (Fv F v) P x b) :=
      continuous_pi fun i => hs.comp ((continuous_apply i).comp (hy b))
    have hrow : Continuous fun x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E =>
        row (sigR (Fv F v) σ) (JR (F := F) (Fv F v) J) (yv (Fv F v) P x b) :=
      hsy.matrix_vecMul continuous_const
    have hrow2 : Continuous fun x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E =>
        cc (E := E) (Fv F v) T b • row (sigR (Fv F v) σ) (JR (F := F) (Fv F v) J) (yv (Fv F v) P x b) -
          row (sigR (Fv F v) σ) (JR (F := F) (Fv F v) J) (wv (Fv F v) P T b) :=
      Continuous.sub (hrow.const_smul (cc (E := E) (Fv F v) T b)) (continuous_const (y := row (sigR (Fv F v) σ) (JR (F := F) (Fv F v) J) (wv (Fv F v) P T b)))
    have h1 : Continuous fun x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E =>
        Matrix.vecMulVec (wv (Fv F v) P T b) (row (sigR (Fv F v) σ) (JR (F := F) (Fv F v) J) (yv (Fv F v) P x b)) :=
      continuous_const.matrix_vecMulVec hrow
    have h2 : Continuous fun x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E =>
        Matrix.vecMulVec (yv (Fv F v) P x b) (cc (E := E) (Fv F v) T b • row (sigR (Fv F v) σ) (JR (F := F) (Fv F v) J) (yv (Fv F v) P x b) -
          row (sigR (Fv F v) σ) (JR (F := F) (Fv F v) J) (wv (Fv F v) P T b)) :=
      (hy b).matrix_vecMulVec hrow2
    exact (continuous_const.add h1).add h2
  have hPm : ∀ k, Continuous fun x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E =>
      Pm (Fv F v) σ J P T x k := by
    intro k
    induction k with
    | zero => simp only [Pm_zero]; exact continuous_const
    | succ k ih =>
      simp only [Pm_succ]
      by_cases hk : k < r + 1
      · simp only [dif_pos hk]
        exact (hMb _).matrix_mul ih
      · simp only [dif_neg hk]
        exact continuous_const.matrix_mul ih
  refine ⟨fun x => mkHA hdet (Pm (Fv F v) σ J P T x (r + 1)) (Pm_unitary x hσ hJ hP (r + 1)), ?_, ?_⟩
  · have hinv : Continuous fun x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E =>
        (JR (F := F) (Fv F v) J)⁻¹ * Formalism.UG.cT (sigR (Fv F v) σ) (Pm (Fv F v) σ J P T x (r + 1)) * JR (F := F) (Fv F v) J := by
      simp only [Formalism.UG.cT]
      exact (continuous_const.matrix_mul ((hPm _).matrix_map hs).matrix_transpose).matrix_mul
        continuous_const
    exact Continuous.subtype_mk (p := fun g => g ∈ HR (Fv F v) σ J)
      (Units.continuous_iff.2 ⟨hPm (r + 1), hinv⟩) _
  · intro x b
    rw [lin_mkHA, unitriangularEichlerPartialProduct_initialVectors x hσ hJ hP, if_pos b.isLt]
    have hco : ∀ a : Fin (r + 1), (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 :
        Fv F v ⊗[F] E) = (if a = b then 1 else 0) + coef (Fv F v) x b a := by
      intro a
      by_cases hab : a = b
      · subst hab; simp [coef]
      · simp [hab, coef]
    simp only [hco, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl

end GlobalTheory.UnitriSection
