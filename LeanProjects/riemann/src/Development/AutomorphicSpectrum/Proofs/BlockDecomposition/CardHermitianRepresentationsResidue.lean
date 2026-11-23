import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardOrthonormalFramesHermitianSpaceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHermitianCongrToOneStatement

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens.Emb

variable {E : Type} [CommRing E] {τ : E →+* E}

theorem cT_mul_rect {a b c : ℕ} (x : Matrix (Fin a) (Fin b) E) (y : Matrix (Fin b) (Fin c) E) :
    cT τ (x * y) = cT τ y * cT τ x := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one_sq {a : ℕ} : cT τ (1 : Matrix (Fin a) (Fin a) E) = 1 := by
  unfold cT
  rw [Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.transpose_one]

theorem card_eq_card_one {m n : ℕ} (S : Matrix (Fin m) (Fin m) E) (T g : Matrix (Fin n) (Fin n) E)
    (hg : IsUnit g.det) (hgT : cT τ g * T * g = 1) :
    Nat.card {x : Matrix (Fin m) (Fin n) E // cT τ x * S * x = T} =
      Nat.card {y : Matrix (Fin m) (Fin n) E // cT τ y * S * y = 1} := by
  have hgh : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hg
  have hhg : cT τ g⁻¹ * cT τ g = 1 := by rw [← cT_mul_rect, hgh, cT_one_sq]
  have hT : T = cT τ g⁻¹ * g⁻¹ := by
    calc T = (cT τ g⁻¹ * cT τ g) * T * (g * g⁻¹) := by rw [hhg, hgh, Matrix.one_mul, Matrix.mul_one]
      _ = cT τ g⁻¹ * (cT τ g * T * g) * g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = cT τ g⁻¹ * g⁻¹ := by rw [hgT, Matrix.mul_one]
  refine Nat.card_congr ⟨fun x => ⟨x.1 * g, ?_⟩, fun y => ⟨y.1 * g⁻¹, ?_⟩, ?_, ?_⟩
  · rw [cT_mul_rect]
    calc cT τ g * cT τ x.1 * S * (x.1 * g) = cT τ g * (cT τ x.1 * S * x.1) * g := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [x.2, hgT]
  · rw [cT_mul_rect]
    calc cT τ g⁻¹ * cT τ y.1 * S * (y.1 * g⁻¹) = cT τ g⁻¹ * (cT τ y.1 * S * y.1) * g⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = T := by rw [y.2, Matrix.mul_one, ← hT]
  · intro x
    apply Subtype.ext
    show x.1 * g * g⁻¹ = x.1
    rw [Matrix.mul_assoc, hgh, Matrix.mul_one]
  · intro y
    apply Subtype.ext
    show y.1 * g⁻¹ * g = y.1
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul g hg, Matrix.mul_one]

theorem card_one_eq_orthonormal (hτ : ∀ a, τ (τ a) = a) {m n : ℕ} (S : Matrix (Fin m) (Fin m) E)
    (hS : cT τ S = S) (hd : IsUnit S.det) :
    Nat.card {y : Matrix (Fin m) (Fin n) E // cT τ y * S * y = 1} =
      Nat.card {x : Fin n → (Fin m → E) //
        ∀ i j, (HermSp.ofMatrix hτ S hS hd).h (x i) (x j) = if i = j then 1 else 0} := by
  refine Nat.card_congr ⟨fun y => ⟨fun j a => y.1 a j, ?_⟩,
    fun x => ⟨Matrix.of (fun a j => x.1 j a), ?_⟩, ?_, ?_⟩
  · intro i j
    have h := gram_apply hτ S hS hd y.1 j i
    rw [y.2, Matrix.one_apply] at h
    rw [← h]
    simp only [eq_comm]
  · ext i j
    rw [gram_apply hτ S hS hd, Matrix.one_apply]
    have h := x.2 j i
    simp only [eq_comm (a := i)]
    exact h
  · intro y
    apply Subtype.ext
    ext a j
    rfl
  · intro x
    apply Subtype.ext
    funext j a
    rfl

theorem prod_pow_div (x : ℝ) (hx : x ≠ 0) (n : ℕ) : ∀ m : ℕ, n ≤ m →
    ∏ i : Fin n, (x ^ (2 * (m - (i : ℕ))) / x) = x ^ (2 * m * n - n ^ 2) := by
  induction n with
  | zero => intro m _; simp
  | succ n ih =>
    intro m hnm
    obtain ⟨k, rfl⟩ : ∃ k, m = n + 1 + k := ⟨m - (n + 1), by omega⟩
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih _ (by omega)]
    have a : 2 * (n + 1 + k) * n - n ^ 2 = n ^ 2 + 2 * n + 2 * k * n := by
      apply Nat.sub_eq_of_eq_add; ring
    have b : 2 * (n + 1 + k) * (n + 1) - (n + 1) ^ 2 = (n + 1) ^ 2 + 2 * k * (n + 1) := by
      apply Nat.sub_eq_of_eq_add; ring
    have c : n + 1 + k - n = k + 1 := by omega
    have d : x ^ (2 * (k + 1)) / x = x ^ (2 * k + 1) := by
      have : x ^ (2 * (k + 1)) = x ^ (2 * k + 1) * x := by ring
      rw [this, mul_div_cancel_right₀ _ hx]
    rw [a, b, c, d, ← pow_add]
    congr 1
    ring

theorem card_isometric_embeddings : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ),
    ResAlg E τ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) E)
    (T : Matrix (Fin n) (Fin n) E), cT τ S = S → IsUnit S.det → cT τ T = T → IsUnit T.det →
    (Nat.card {x : Matrix (Fin m) (Fin n) E // cT τ x * S * x = T} : ℝ) =
      (q : ℝ) ^ (2 * m * n - n ^ 2) * ∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ))) := by
  intro E _ τ q ε hR m n hnm S T hS hSd hT hTd
  obtain ⟨g, hg, hgT⟩ := GlobalTheory.T.exists_hermitian_congr_to_one E τ q ε hR n T hT hTd
  have hcard : Nat.card (Fin m → E) = q ^ (2 * m) := by
    rw [Nat.card_fun, hR.card, Nat.card_eq_fintype_card, Fintype.card_fin, pow_mul]
  have hq : (q : ℝ) ≠ 0 := by
    have := hR.one_lt
    exact_mod_cast (by omega : q ≠ 0)
  rw [card_eq_card_one S T g hg hgT, card_one_eq_orthonormal hR.inv S hS hSd,
    GlobalTheory.T.card_orthonormal_frames_hermitian_space E τ q ε hR n m hnm (Fin m → E) (HermSp.ofMatrix hR.inv S hS hSd) hcard,
    Finset.prod_mul_distrib, prod_pow_div _ hq n m hnm]

end GlobalTheory.CompanionTheory.UnrDens.Emb
