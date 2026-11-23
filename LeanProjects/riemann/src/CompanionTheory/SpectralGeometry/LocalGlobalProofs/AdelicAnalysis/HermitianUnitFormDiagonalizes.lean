import Mathlib
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinatePolynomialsFormMemKernelDifferential
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.RingDiag

open HeckeCharacterZeroLocus.SiegelWeilU

variable {A : Type} [CommRing A] {m : ℕ}

def bd (a : A) (M : Matrix (Fin m) (Fin m) A) : Matrix (Fin (m + 1)) (Fin (m + 1)) A :=
  fun i j => Fin.cases (Fin.cases a (fun _ => 0) j)
    (fun i' => Fin.cases 0 (fun j' => M i' j') j) i

@[simp] lemma bd_zero_zero (a : A) (M : Matrix (Fin m) (Fin m) A) : bd a M 0 0 = a := rfl
@[simp] lemma bd_zero_succ (a : A) (M : Matrix (Fin m) (Fin m) A) (j : Fin m) :
    bd a M 0 j.succ = 0 := rfl
@[simp] lemma bd_succ_zero (a : A) (M : Matrix (Fin m) (Fin m) A) (i : Fin m) :
    bd a M i.succ 0 = 0 := rfl
@[simp] lemma bd_succ_succ (a : A) (M : Matrix (Fin m) (Fin m) A) (i j : Fin m) :
    bd a M i.succ j.succ = M i j := rfl

lemma bd_mul (a b : A) (M N : Matrix (Fin m) (Fin m) A) :
    bd a M * bd b N = bd (a * b) (M * N) := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

lemma det_bd (a : A) (M : Matrix (Fin m) (Fin m) A) : (bd a M).det = a * M.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have : (bd a M).submatrix Fin.succ Fin.succ = M := by
    ext i j; simp
  simp [this]

lemma cT_bd (σ : A →+* A) (a : A) (M : Matrix (Fin m) (Fin m) A) :
    cT σ (bd a M) = bd (σ a) (cT σ M) := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [cT]

lemma bd_diagonal (a : A) (d : Fin m → A) :
    bd a (Matrix.diagonal d) = Matrix.diagonal (Fin.cons a d : Fin (m + 1) → A) := by
  have h0 : ∀ j' : Fin m, (0 : Fin (m + 1)) ≠ j'.succ := fun j' => (Fin.succ_ne_zero j').symm
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [Matrix.diagonal_apply, h0]

def uni (r : Fin m → A) : Matrix (Fin (m + 1)) (Fin (m + 1)) A :=
  fun i j => Fin.cases (Fin.cases 1 r j)
    (fun i' => Fin.cases 0 (fun j' => (1 : Matrix (Fin m) (Fin m) A) i' j') j) i

@[simp] lemma uni_zero_zero (r : Fin m → A) : uni r 0 0 = 1 := rfl
@[simp] lemma uni_zero_succ (r : Fin m → A) (j : Fin m) : uni r 0 j.succ = r j := rfl
@[simp] lemma uni_succ_zero (r : Fin m → A) (i : Fin m) : uni r i.succ 0 = 0 := rfl
@[simp] lemma uni_succ_succ (r : Fin m → A) (i j : Fin m) :
    uni r i.succ j.succ = (1 : Matrix (Fin m) (Fin m) A) i j := rfl

lemma det_uni (r : Fin m → A) : (uni r).det = 1 := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have : (uni r).submatrix Fin.succ Fin.succ = 1 := by
    ext i j; simp
  simp [this]

def schur (K : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (b : A) : Matrix (Fin m) (Fin m) A :=
  fun i j => K i.succ j.succ - K i.succ 0 * b * K 0 j.succ

lemma mul_uni (K : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (r : Fin m → A) (i : Fin (m + 1)) :
    (K * uni r) i 0 = K i 0 ∧ ∀ j : Fin m, (K * uni r) i j.succ = K i j.succ + K i 0 * r j := by
  constructor
  · simp [Matrix.mul_apply, Fin.sum_univ_succ]
  · intro j
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, add_comm]

lemma cT_uni_mul (σ : A →+* A) (P : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (r : Fin m → A)
    (j : Fin (m + 1)) :
    (cT σ (uni r) * P) 0 j = P 0 j ∧
      ∀ i : Fin m, (cT σ (uni r) * P) i.succ j = P i.succ j + σ (r i) * P 0 j := by
  constructor
  · simp [cT, Matrix.mul_apply, Fin.sum_univ_succ]
  · intro i
    simp [cT, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, add_comm,
      apply_ite σ]

lemma schur_step (σ : A →+* A) (K : Matrix (Fin (m + 1)) (Fin (m + 1)) A)
    (hK : ∀ i j, σ (K j i) = K i j) (b : A) (hb : b * K 0 0 = 1) (hσb : σ b = b) :
    cT σ (uni fun j => -(b * K 0 j.succ)) * K * (uni fun j => -(b * K 0 j.succ)) =
      bd (K 0 0) (schur K b) := by
  set r : Fin m → A := fun j => -(b * K 0 j.succ) with hr
  have hσr : ∀ i, σ (r i) = -(b * K i.succ 0) := by
    intro i; simp [hr, hσb, hK]
  have hzero : ∀ j : Fin m, K 0 j.succ + K 0 0 * r j = 0 := by
    intro j
    have : K 0 0 * r j = -((b * K 0 0) * K 0 j.succ) := by simp only [hr]; ring
    rw [this, hb]; ring
  rw [Matrix.mul_assoc]
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · rw [(cT_uni_mul σ _ r 0).1, (mul_uni K r 0).1]; simp
  · rw [(cT_uni_mul σ _ r _).1, (mul_uni K r 0).2, hzero]; simp
  · rw [(cT_uni_mul σ _ r 0).2, (mul_uni K r _).1, (mul_uni K r 0).1, hσr]
    simp only [bd_succ_zero]
    have : b * K i'.succ 0 * K 0 0 = (b * K 0 0) * K i'.succ 0 := by ring
    rw [neg_mul, this, hb]; ring
  · rw [(cT_uni_mul σ _ r _).2, (mul_uni K r _).2, (mul_uni K r 0).2, hzero, hσr]
    simp only [bd_succ_succ, schur, hr]; ring

lemma det_cT (σ : A →+* A) (g : Matrix (Fin m) (Fin m) A) : (cT σ g).det = σ g.det := by
  rw [cT, Matrix.det_transpose, RingHom.map_det]; rfl

lemma cT_cT (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y) {p q : Type}
    (M : Matrix p q A) : cT σ (cT σ M) = M := by
  ext i j; simp [cT, hσ]

lemma cT_congr_herm (σ : A →+* A) {n : ℕ} (hσ : ∀ y, σ (σ y) = y)
    (J g : Matrix (Fin n) (Fin n) A) (hJ : ∀ i j, σ (J j i) = J i j) :
    ∀ i j, σ ((cT σ g * J * g) j i) = (cT σ g * J * g) i j := by
  have hJ' : cT σ J = J := by ext i j; exact hJ i j
  have : cT σ (cT σ g * J * g) = cT σ g * J * g := by
    rw [cT_mul, cT_mul, cT_cT σ hσ, hJ', Matrix.mul_assoc]
  intro i j
  exact congrFun (congrFun this i) j

lemma corner (σ : A →+* A) {n : ℕ} (J g : Matrix (Fin (n + 1)) (Fin (n + 1)) A)
    (x : Fin (n + 1) → A) (hg : ∀ i, g i 0 = x i) :
    (cT σ g * J * g) 0 0 = hform σ J x x := by
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, hg, hform,
    Finset.sum_mul]
  exact Finset.sum_comm

lemma unimodular (σ : A →+* A) {n : ℕ} (J : Matrix (Fin n) (Fin n) A) (x : Fin n → A) (b : A)
    (hb : b * hform σ J x x = 1) : ∃ c : Fin n → A, ∑ i, c i * x i = 1 := by
  refine ⟨fun j => b * ∑ i, σ (x i) * J i j, ?_⟩
  rw [← hb, hform, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show (b * ∑ i : Fin n, σ (x i) * J i j) * x j = b * ∑ i : Fin n, σ (x i) * J i j * x j
  rw [mul_assoc, Finset.sum_mul]

theorem diagonalise : ∀ (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A), (∀ y, σ (σ y) = y) → (∀ (m : ℕ) (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A), (∀ i j, σ (J j i) = J i j) → IsUnit J.det → ∃ x, IsUnit (HeckeCharacterZeroLocus.SiegelWeilU.hform σ J x x)) → ∀ (m : ℕ) (J : Matrix (Fin m) (Fin m) A), (∀ i j, σ (J j i) = J i j) → IsUnit J.det → ∃ (g : Matrix (Fin m) (Fin m) A) (d : Fin m → A), IsUnit g.det ∧ (∀ i, IsUnit (d i) ∧ σ (d i) = d i) ∧ HeckeCharacterZeroLocus.SiegelWeilU.cT σ g * J * g = Matrix.diagonal d := by
  intro A _ _ σ hσ H m
  induction m with
  | zero =>
    intro J _ _
    exact ⟨1, Fin.elim0, by simp, fun i => i.elim0, by ext i; exact i.elim0⟩
  | succ m ih =>
    intro J hJ hdet
    obtain ⟨x, hx⟩ := H m J hJ hdet
    obtain ⟨b, hb⟩ := hx.exists_left_inv
    obtain ⟨g₀, hg₀, hcol⟩ := GlobalTheory.CompanionTheory.SW.SemilocalColumn.exists_invertible_first_column A m x (unimodular σ J x b hb)
    set K := cT σ g₀ * J * g₀ with hKdef
    have hK : ∀ i j, σ (K j i) = K i j := cT_congr_herm σ hσ J g₀ hJ
    have hcorner : K 0 0 = hform σ J x x := corner σ J g₀ x hcol
    have hbK : b * K 0 0 = 1 := by rw [hcorner]; exact hb
    have hβ : IsUnit (K 0 0) := by rw [hcorner]; exact hx
    have hσβ : σ (K 0 0) = K 0 0 := hK 0 0
    have hσb : σ b = b := by
      have h1 : σ b * K 0 0 = 1 := by
        have := congrArg σ hbK
        rwa [map_mul, hσβ, map_one] at this
      calc σ b = σ b * (K 0 0 * b) := by rw [mul_comm (K 0 0), hbK, mul_one]
        _ = (σ b * K 0 0) * b := by ring
        _ = b := by rw [h1, one_mul]
    set r : Fin m → A := fun j => -(b * K 0 j.succ) with hr
    have hstep := schur_step σ K hK b hbK hσb
    have hKdet : IsUnit K.det := by
      rw [hKdef, Matrix.det_mul, Matrix.det_mul, det_cT]
      exact ((hg₀.map σ).mul hdet).mul hg₀
    have hJ₁det : IsUnit (schur K b).det := by
      have h2 : (K 0 0) * (schur K b).det = K.det := by
        rw [← det_bd, ← hstep, Matrix.det_mul, Matrix.det_mul, det_cT, det_uni]; simp
      rw [← h2] at hKdet
      exact isUnit_of_mul_isUnit_right hKdet
    have hJ₁ : ∀ i j, σ (schur K b j i) = schur K b i j := by
      intro i j
      simp only [schur, map_sub, map_mul, hσb, hK]
      ring
    obtain ⟨g₁, d₁, hg₁, hd₁, hdiag⟩ := ih (schur K b) hJ₁ hJ₁det
    refine ⟨g₀ * uni r * bd 1 g₁, Fin.cons (K 0 0) d₁, ?_, ?_, ?_⟩
    · rw [Matrix.det_mul, Matrix.det_mul, det_uni, det_bd]
      simpa using hg₀.mul hg₁
    · intro i
      refine Fin.cases ?_ (fun i' => ?_) i
      · simpa using ⟨hβ, hσβ⟩
      · simpa using hd₁ i'
    · have e : cT σ (g₀ * uni r * bd 1 g₁) * J * (g₀ * uni r * bd 1 g₁) =
          cT σ (bd 1 g₁) * (cT σ (uni r) * K * uni r) * bd 1 g₁ := by
        rw [hKdef, cT_mul, cT_mul]
        simp only [Matrix.mul_assoc]
      rw [e, hstep, cT_bd, bd_mul, bd_mul, hdiag, map_one, one_mul, mul_one, bd_diagonal]

end GlobalTheory.CompanionTheory.SW.RingDiag
