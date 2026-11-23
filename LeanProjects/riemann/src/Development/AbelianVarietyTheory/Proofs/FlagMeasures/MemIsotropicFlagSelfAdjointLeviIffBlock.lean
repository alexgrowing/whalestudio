import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Formalism.REAL (Jm UJ inUJ Jm_mul_self Jm_conjTranspose)

namespace GlobalTheory.LeviIso.Range

variable {n n₀ a : ℕ} {j : Fin a → ℕ} {ε : Fin n → Bool} {ε₀ : Fin n₀ → Bool}
  {B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ} {B₀ : Matrix (Fin n) (Fin n₀) ℂ}
  {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}

theorem ext_mulVec {p q : ℕ} {M N : Matrix (Fin p) (Fin q) ℂ} (h : ∀ v, M *ᵥ v = N *ᵥ v) : M = N := by
  exact Matrix.mulVec_injective (funext h)

theorem proj (h : IsFrame ε ε₀ B B₀) (u : ∀ i, Fin (j i) → ℂ) (k : Fin a) :
    (B k)ᴴ *ᵥ ∑ l, B l *ᵥ u l = u k := by
  rw [Matrix.mulVec_sum, Finset.sum_eq_single k]
  · rw [Matrix.mulVec_mulVec, h.1 k, Matrix.one_mulVec]
  · intro l _ hl
    rw [Matrix.mulVec_mulVec, h.2.1 k l (Ne.symm hl), Matrix.zero_mulVec]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem col_mem (hW : SpansFlag B W) (i : Fin a) (v : Fin (j i) → ℂ) : B i *ᵥ v ∈ W i.succ := by
  classical
  rw [hW]
  refine ⟨Pi.single i v, fun l hl => ?_, ?_⟩
  · have hne : l ≠ i := by
      rintro rfl
      exact hl (by simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega)
    exact Pi.single_eq_of_ne (M := fun l => Fin (j l) → ℂ) hne v
  · rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]
    · intro l _ hl
      rw [Pi.single_eq_of_ne (M := fun l => Fin (j l) → ℂ) hl, Matrix.mulVec_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi

theorem upper (h : IsFrame ε ε₀ B B₀) (hW : SpansFlag B W) {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ k, ∀ y ∈ W k, M *ᵥ y ∈ W k) {i k : Fin a} (hik : i < k) : (B k)ᴴ * M * B i = 0 := by
  apply ext_mulVec
  intro v
  rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  obtain ⟨u, hu, hyu⟩ := (hW _ _).1 (hM _ _ (col_mem hW i v))
  rw [hyu, proj h]
  apply hu
  intro hlt
  have hik' := Fin.lt_def.1 hik
  simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at hlt
  omega

theorem expand (h : IsFrame ε ε₀ B B₀) (hW : SpansFlag B W) {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ k, ∀ y ∈ W k, M *ᵥ y ∈ W k) (i : Fin a) : M * B i = ∑ k, B k * ((B k)ᴴ * M * B i) := by
  apply ext_mulVec
  intro v
  obtain ⟨u, -, hyu⟩ := (hW _ _).1 (hM _ _ (col_mem hW i v))
  have hk : ∀ k, (B k * ((B k)ᴴ * M * B i)) *ᵥ v = B k *ᵥ u k := by
    intro k
    have e : (B k * ((B k)ᴴ * M * B i)) *ᵥ v = B k *ᵥ ((B k)ᴴ *ᵥ (M *ᵥ (B i *ᵥ v))) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [e, hyu, proj h]
  rw [Matrix.sum_mulVec, Finset.sum_congr rfl (fun k _ => hk k), ← hyu, Matrix.mulVec_mulVec]

theorem diag (h : IsFrame ε ε₀ B B₀) (hW : SpansFlag B W) {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ k, ∀ y ∈ W k, M *ᵥ y ∈ W k) (hM' : ∀ k, ∀ y ∈ W k, Mᴴ *ᵥ y ∈ W k) (i : Fin a) :
    M * B i = B i * ((B i)ᴴ * M * B i) := by
  rw [expand h hW hM i, Finset.sum_eq_single i]
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hlt | hgt
    · have e := upper h hW hM' hlt
      have e' : (B k)ᴴ * M * B i = 0 := by
        have := congrArg Matrix.conjTranspose e
        simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using this
      rw [e', Matrix.mul_zero]
    · rw [upper h hW hM hgt, Matrix.mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem lev_keeps (h : IsFrame ε ε₀ B B₀) (hW : SpansFlag B W) (x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ)
    (g : Matrix (Fin n₀) (Fin n₀) ℂ) (k : Fin (a + 1)) (y : Fin n → ℂ) (hy : y ∈ W k) :
    lev ε B B₀ x g *ᵥ y ∈ W k := by
  obtain ⟨u, hu, rfl⟩ := (hW _ _).1 hy
  rw [hW]
  refine ⟨fun i => x i *ᵥ u i, fun i hi => by
    show x i *ᵥ u i = 0
    rw [hu i hi, Matrix.mulVec_zero], ?_⟩
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mulVec_mulVec, h.lev_mul_B x g i]

theorem left_inv {p : ℕ} {ε : Fin p → Bool} {M : Matrix (Fin p) (Fin p) ℂ} (hU : Mᴴ * Jm ε * M = Jm ε) :
    Jm ε * Mᴴ * Jm ε * M = 1 := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hU, Jm_mul_self]

theorem block (h : IsFrame ε ε₀ B B₀) {M : Matrix (Fin n) (Fin n) ℂ} (hU : Mᴴ * Jm ε * M = Jm ε)
    {x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ} (h1 : ∀ i, M * B i = B i * x i)
    (h2 : ∀ i, Mᴴ * B i = B i * (x i)ᴴ) :
    (∀ i, (x i).det ≠ 0) ∧ inUJ ε₀ (B₀ᴴ * M * B₀) ∧ M = lev ε B B₀ x (B₀ᴴ * M * B₀) := by
  have hJJ : Jm ε * Jm ε = 1 := Jm_mul_self ε
  have hJH : (Jm ε)ᴴ = Jm ε := Jm_conjTranspose ε
  have hR : M * (Jm ε * Mᴴ * Jm ε) = 1 := mul_eq_one_comm.1 (left_inv hU)
  have hMJ : M * Jm ε * Mᴴ = Jm ε := by
    calc M * Jm ε * Mᴴ = M * (Jm ε * Mᴴ * Jm ε) * Jm ε := by
          simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = Jm ε := by rw [hR, Matrix.one_mul]
  have hy : ∀ i, ((B i)ᴴ * Jm ε * Mᴴ * Jm ε * B i) * x i = 1 := by
    intro i
    calc ((B i)ᴴ * Jm ε * Mᴴ * Jm ε * B i) * x i
        = (B i)ᴴ * Jm ε * (Mᴴ * Jm ε * (B i * x i)) := by simp only [Matrix.mul_assoc]
      _ = (B i)ᴴ * Jm ε * (Mᴴ * Jm ε * (M * B i)) := by rw [h1]
      _ = (B i)ᴴ * (Jm ε * Jm ε) * B i := by
          rw [← Matrix.mul_assoc (Mᴴ * Jm ε), hU]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJJ, Matrix.mul_one, h.1 i]
  have hdet : ∀ i, (x i).det ≠ 0 := fun i => Matrix.det_ne_zero_of_left_inverse (hy i)
  have hdetU : ∀ i, IsUnit (x i).det := fun i => isUnit_iff_ne_zero.2 (hdet i)
  have hA : ∀ i, Mᴴ * Jm ε * B i = Jm ε * B i * (x i)⁻¹ := by
    intro i
    have e : Mᴴ * Jm ε * B i * x i = Jm ε * B i := by
      rw [Matrix.mul_assoc (Mᴴ * Jm ε) (B i) (x i), ← h1 i, ← Matrix.mul_assoc (Mᴴ * Jm ε) M (B i), hU]
    calc Mᴴ * Jm ε * B i = Mᴴ * Jm ε * B i * x i * (x i)⁻¹ :=
          (Matrix.mul_nonsing_inv_cancel_right (x i) _ (hdetU i)).symm
      _ = Jm ε * B i * (x i)⁻¹ := by rw [e]
  have hC : ∀ i, M * (Jm ε * B i) = Jm ε * B i * (x i)⁻¹ᴴ := by
    intro i
    have e : M * (Jm ε * B i) * (x i)ᴴ = Jm ε * B i := by
      calc M * (Jm ε * B i) * (x i)ᴴ = M * Jm ε * (B i * (x i)ᴴ) := by simp only [Matrix.mul_assoc]
        _ = M * Jm ε * (Mᴴ * B i) := by rw [h2]
        _ = (M * Jm ε * Mᴴ) * B i := by simp only [Matrix.mul_assoc]
        _ = Jm ε * B i := by rw [hMJ]
    have hu : IsUnit ((x i)ᴴ).det := by
      rw [Matrix.det_conjTranspose]
      exact isUnit_iff_ne_zero.2 (star_ne_zero.2 (hdet i))
    calc M * (Jm ε * B i) = M * (Jm ε * B i) * (x i)ᴴ * ((x i)ᴴ)⁻¹ :=
          (Matrix.mul_nonsing_inv_cancel_right ((x i)ᴴ) _ hu).symm
      _ = Jm ε * B i * (x i)⁻¹ᴴ := by rw [e, Matrix.conjTranspose_nonsing_inv]
  have e1 : ∀ i, (B i)ᴴ * (M * B₀) = 0 := by
    intro i
    have hBM : (B i)ᴴ * M = x i * (B i)ᴴ := by
      have := congrArg Matrix.conjTranspose (h2 i)
      simpa [Matrix.conjTranspose_mul] using this
    rw [← Matrix.mul_assoc, hBM, Matrix.mul_assoc, h.2.2.2.1 i, Matrix.mul_zero]
  have e2 : ∀ i, (B i)ᴴ * Jm ε * (M * B₀) = 0 := by
    intro i
    have hBJM : (B i)ᴴ * Jm ε * M = ((x i)⁻¹)ᴴ * ((B i)ᴴ * Jm ε) := by
      have := congrArg Matrix.conjTranspose (hA i)
      simpa [Matrix.conjTranspose_mul, hJH, Matrix.mul_assoc] using this
    rw [← Matrix.mul_assoc, hBJM, Matrix.mul_assoc, h.J_B₀ i, Matrix.mul_zero]
  have hD : M * B₀ = B₀ * (B₀ᴴ * M * B₀) := by
    have s1 : ∀ i, B i * (B i)ᴴ * (M * B₀) = 0 := fun i => by
      rw [Matrix.mul_assoc, e1 i, Matrix.mul_zero]
    have s2 : ∀ i, Jm ε * B i * (B i)ᴴ * Jm ε * (M * B₀) = 0 := fun i => by
      rw [show Jm ε * B i * (B i)ᴴ * Jm ε * (M * B₀) = Jm ε * B i * ((B i)ᴴ * Jm ε * (M * B₀)) by
        simp only [Matrix.mul_assoc], e2 i, Matrix.mul_zero]
    calc M * B₀ = (∑ i, B i * (B i)ᴴ + ∑ i, Jm ε * B i * (B i)ᴴ * Jm ε + B₀ * B₀ᴴ) * (M * B₀) := by
          rw [h.2.2.2.2.2.2, Matrix.one_mul]
      _ = B₀ * (B₀ᴴ * M * B₀) := by
          rw [Matrix.add_mul, Matrix.add_mul, Matrix.sum_mul, Matrix.sum_mul]
          simp only [s1, s2, Finset.sum_const_zero, zero_add]
          simp only [Matrix.mul_assoc]
  have hJB₀ : Jm ε * B₀ = B₀ * Jm ε₀ := h.2.2.2.2.2.1
  have hE : inUJ ε₀ (B₀ᴴ * M * B₀) := by
    show (B₀ᴴ * M * B₀)ᴴ * Jm ε₀ * (B₀ᴴ * M * B₀) = Jm ε₀
    calc (B₀ᴴ * M * B₀)ᴴ * Jm ε₀ * (B₀ᴴ * M * B₀)
        = B₀ᴴ * Mᴴ * (B₀ * Jm ε₀) * (B₀ᴴ * M * B₀) := by
          simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = B₀ᴴ * Mᴴ * Jm ε * (B₀ * (B₀ᴴ * M * B₀)) := by
          rw [← hJB₀]
          simp only [Matrix.mul_assoc]
      _ = B₀ᴴ * (Mᴴ * Jm ε * M) * B₀ := by
          rw [← hD]
          simp only [Matrix.mul_assoc]
      _ = B₀ᴴ * B₀ * Jm ε₀ := by
          rw [hU, Matrix.mul_assoc, hJB₀, ← Matrix.mul_assoc]
      _ = Jm ε₀ := by rw [h.2.2.2.2.1, Matrix.one_mul]
  refine ⟨hdet, hE, ?_⟩
  apply h.ext
  · intro i
    rw [h1 i, h.lev_mul_B]
  · intro i
    rw [hC i, h.lev_mul_JB]
  · rw [hD, h.lev_mul_B₀]

theorem mem_flagM_iff : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool)
    (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ →
    ∀ W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ), SpansFlag B W → ∀ m : Formalism.REAL.UJ ε,
      m ∈ flagM ε W ↔ ∃ (x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (g : Formalism.REAL.UJ ε₀),
        (∀ i, (x i).det ≠ 0) ∧ uMat m = lev ε B B₀ x (uMat g) := by
  intro n n₀ a j ε ε₀ B B₀ h W hW m
  constructor
  · intro hm
    have hm' : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i ∧ (uMat m)ᴴ *ᵥ y ∈ W i := hm
    have hM : ∀ k, ∀ y ∈ W k, uMat m *ᵥ y ∈ W k := fun k y hy => (hm' k y hy).1
    have hM' : ∀ k, ∀ y ∈ W k, (uMat m)ᴴ *ᵥ y ∈ W k := fun k y hy => (hm' k y hy).2
    have hM'' : ∀ k, ∀ y ∈ W k, (uMat m)ᴴᴴ *ᵥ y ∈ W k := by
      intro k y hy
      rw [Matrix.conjTranspose_conjTranspose]
      exact hM k y hy
    have hU : (uMat m)ᴴ * Jm ε * uMat m = Jm ε := m.2
    have h2 : ∀ i, (uMat m)ᴴ * B i = B i * ((B i)ᴴ * uMat m * B i)ᴴ := by
      intro i
      rw [diag h hW hM' hM'' i]
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    obtain ⟨hdet, hE, heq⟩ := block h hU (x := fun i => (B i)ᴴ * uMat m * B i)
      (fun i => diag h hW hM hM' i) h2
    have hinv : (Jm ε₀ * (B₀ᴴ * uMat m * B₀)ᴴ * Jm ε₀) * (B₀ᴴ * uMat m * B₀) = 1 := left_inv hE
    have hinv' : (B₀ᴴ * uMat m * B₀) * (Jm ε₀ * (B₀ᴴ * uMat m * B₀)ᴴ * Jm ε₀) = 1 :=
      mul_eq_one_comm.1 hinv
    refine ⟨fun i => (B i)ᴴ * uMat m * B i,
      ⟨⟨B₀ᴴ * uMat m * B₀, Jm ε₀ * (B₀ᴴ * uMat m * B₀)ᴴ * Jm ε₀, hinv', hinv⟩, hE⟩, hdet, ?_⟩
    exact heq
  · rintro ⟨x, g, -, hmg⟩
    show ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i ∧ (uMat m)ᴴ *ᵥ y ∈ W i
    intro k y hy
    rw [hmg]
    refine ⟨lev_keeps h hW x (uMat g) k y hy, ?_⟩
    rw [lev_conjTranspose]
    exact lev_keeps h hW _ _ k y hy

end GlobalTheory.LeviIso.Range
