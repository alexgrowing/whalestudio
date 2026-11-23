import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBoxRadiiAtEntry

open ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.NormalCore

noncomputable section
namespace GlobalTheory.NormalCore.UnipMove

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_mul_le {ϖ : kˣ} (hϖ : IsUnif ϖ) {N : ℕ} (hN : 1 ≤ N) {a b : k}
    (ha : valuation k a ≤ valuation k ((ϖ ^ N : kˣ) : k)) (hb : valuation k b ≤ valuation k ((ϖ ^ N : kˣ) : k)) :
    valuation k (a * b) ≤ valuation k ((ϖ ^ (N + 1) : kˣ) : k) := by
  rw [map_mul]
  refine (mul_le_mul' ha hb).trans ?_
  simp only [Units.val_pow_eq_pow_val, map_pow, ← pow_add]
  exact pow_le_pow_right_of_le_one' hϖ.mem (by omega)

theorem val_le_of_le {ϖ : kˣ} (hϖ : IsUnif ϖ) {a b : ℕ} (h : a ≤ b) :
    valuation k ((ϖ ^ b : kˣ) : k) ≤ valuation k ((ϖ ^ a : kˣ) : k) := by
  simp only [Units.val_pow_eq_pow_val, map_pow]
  exact pow_le_pow_right_of_le_one' hϖ.mem h

theorem val_int_mul {ϖ : kˣ} {N : ℕ} {a b : k} (ha : valuation k a ≤ 1)
    (hb : valuation k b ≤ valuation k ((ϖ ^ N : kˣ) : k)) :
    valuation k (a * b) ≤ valuation k ((ϖ ^ N : kˣ) : k) := by
  rw [map_mul]; exact (mul_le_mul' ha hb).trans (by rw [one_mul])

theorem mem_ebox_iff_sub {m l : ℕ} {ϖ : kˣ} {C X : Matrix (Fin m) (Fin l) k} {r : Fin m → Fin l → ℕ} :
    X ∈ ebox ϖ C r ↔ X - C ∈ ebox ϖ 0 r := by
  simp [ebox]

theorem mem_ebox_zero {m l : ℕ} {ϖ : kˣ} {X : Matrix (Fin m) (Fin l) k} {r : Fin m → Fin l → ℕ} :
    X ∈ ebox ϖ 0 r ↔ ∀ i j, valuation k (X i j) ≤ valuation k ((ϖ ^ r i j : kˣ) : k) := by
  simp [ebox]

theorem ebox_zero_add {m l : ℕ} {ϖ : kˣ} {X Y : Matrix (Fin m) (Fin l) k} {r : Fin m → Fin l → ℕ}
    (hX : X ∈ ebox ϖ 0 r) (hY : Y ∈ ebox ϖ 0 r) : X + Y ∈ ebox ϖ 0 r := by
  rw [mem_ebox_zero] at *
  intro i j; exact Valuation.map_add_le _ (hX i j) (hY i j)

theorem ebox_zero_sub {m l : ℕ} {ϖ : kˣ} {X Y : Matrix (Fin m) (Fin l) k} {r : Fin m → Fin l → ℕ}
    (hX : X ∈ ebox ϖ 0 r) (hY : Y ∈ ebox ϖ 0 r) : X - Y ∈ ebox ϖ 0 r := by
  rw [mem_ebox_zero] at *
  intro i j; exact Valuation.map_sub_le _ (hX i j) (hY i j)

theorem ebox_zero_add_small {m l : ℕ} {ϖ : kˣ} (hϖ : IsUnif ϖ) {N : ℕ} {r : Fin m → Fin l → ℕ}
    (hr : ∀ i j, N ≤ r i j ∧ r i j ≤ N + 1) {X M : Matrix (Fin m) (Fin l) k} (hX : X ∈ ebox ϖ 0 r)
    (hM : ∀ i j, valuation k (M i j) ≤ valuation k ((ϖ ^ (N + 1) : kˣ) : k)) : X + M ∈ ebox ϖ 0 r :=
  ebox_zero_add hX (mem_ebox_zero.2 fun i j => (hM i j).trans (val_le_of_le hϖ (hr i j).2))

theorem ebox_zero_le {m l : ℕ} {ϖ : kˣ} (hϖ : IsUnif ϖ) {N : ℕ} {r : Fin m → Fin l → ℕ}
    (hr : ∀ i j, N ≤ r i j ∧ r i j ≤ N + 1) {X : Matrix (Fin m) (Fin l) k} (hX : X ∈ ebox ϖ 0 r) (i : Fin m)
    (j : Fin l) : valuation k (X i j) ≤ valuation k ((ϖ ^ N : kˣ) : k) :=
  (mem_ebox_zero.1 hX i j).trans (val_le_of_le hϖ (hr i j).1)

theorem mul_tv_mem {m l : ℕ} {ϖ : kˣ} (hϖ : IsUnif ϖ) {N : ℕ} (hN : 1 ≤ N) {r : Fin m → Fin l → ℕ}
    (hr : ∀ i j, N ≤ r i j ∧ r i j ≤ N + 1) {t : Fin l → k}
    (ht : ∀ j, valuation k (t j) ≤ valuation k ((ϖ ^ N : kˣ) : k)) (j₀ : Fin l) {X : Matrix (Fin m) (Fin l) k}
    (hX : X ∈ ebox ϖ 0 r) : X * (1 + vecMulVec t (Pi.single j₀ 1)) ∈ ebox ϖ 0 r := by
  rw [Matrix.mul_add, Matrix.mul_one, mul_vecMulVec]
  refine ebox_zero_add_small hϖ hr hX fun i j => ?_
  rw [vecMulVec_apply]
  have h1 : valuation k ((X *ᵥ t) i) ≤ valuation k ((ϖ ^ (N + 1) : kˣ) : k) :=
    by
      simp only [mulVec, dotProduct]
      exact Valuation.map_sum_le _ fun l _ => val_mul_le hϖ hN (ebox_zero_le hϖ hr hX i l) (ht l)
  by_cases hj : j = j₀
  · subst hj; simpa using h1
  · simp [Pi.single_apply, hj]

theorem tv_mul_mem {m l : ℕ} {ϖ : kˣ} (hϖ : IsUnif ϖ) {N : ℕ} (hN : 1 ≤ N) {r : Fin m → Fin l → ℕ}
    (hr : ∀ i j, N ≤ r i j ∧ r i j ≤ N + 1) {t : Fin m → k}
    (ht : ∀ i, valuation k (t i) ≤ valuation k ((ϖ ^ N : kˣ) : k)) (i₀ : Fin m) {X : Matrix (Fin m) (Fin l) k}
    (hX : X ∈ ebox ϖ 0 r) : (1 + vecMulVec t (Pi.single i₀ 1)) * X ∈ ebox ϖ 0 r := by
  rw [Matrix.add_mul, Matrix.one_mul, vecMulVec_mul, single_one_vecMul]
  exact ebox_zero_add_small hϖ hr hX fun i j => by
    rw [vecMulVec_apply]; exact val_mul_le hϖ hN (ht i) (ebox_zero_le hϖ hr hX i₀ j)

theorem tv_mul_tv_neg {m : ℕ} (a b : Fin m → k) (h : b ⬝ᵥ a = 0) :
    (1 + vecMulVec a b) * (1 + vecMulVec (-a) b) = 1 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, vecMulVec_mul_vecMulVec, dotProduct_neg, h,
    neg_zero, zero_smul]
  ext i j; simp [vecMulVec_apply]

theorem tv_neg_mul_tv {m : ℕ} (a b : Fin m → k) (h : b ⬝ᵥ a = 0) :
    (1 + vecMulVec (-a) b) * (1 + vecMulVec a b) = 1 := by
  simpa using tv_mul_tv_neg (-a) b (by simp [h])

theorem preimage_ebox_eq {m l : ℕ} {ϖ : kˣ} {r : Fin m → Fin l → ℕ} {A A' : Matrix (Fin m) (Fin m) k}
    {B B' : Matrix (Fin l) (Fin l) k} {p q x : Matrix (Fin m) (Fin l) k} (hA : A' * A = 1) (hB : B * B' = 1)
    (hpres : ∀ δ ∈ ebox ϖ 0 r, A * δ * B ∈ ebox ϖ 0 r) (hpres' : ∀ δ ∈ ebox ϖ 0 r, A' * δ * B' ∈ ebox ϖ 0 r)
    (hq : A * q * B = p) (hxq : x - q ∈ ebox ϖ 0 r) : {Y | A * Y * B ∈ ebox ϖ p r} = ebox ϖ x r := by
  ext Y
  show A * Y * B ∈ ebox ϖ p r ↔ Y ∈ ebox ϖ x r
  rw [mem_ebox_iff_sub, mem_ebox_iff_sub (C := x)]
  have e1 : A * Y * B - p = A * (Y - x) * B + A * (x - q) * B := by
    rw [← hq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_mul]; abel
  have hx' := hpres _ hxq
  constructor
  · intro h
    have h1 : A * (Y - x) * B ∈ ebox ϖ 0 r := by
      have := ebox_zero_sub h hx'; rwa [e1, add_sub_cancel_right] at this
    have h2 := hpres' _ h1
    have e2 : A' * (A * (Y - x) * B) * B' = Y - x := by
      calc A' * (A * (Y - x) * B) * B' = (A' * A) * (Y - x) * (B * B') := by simp only [Matrix.mul_assoc]
        _ = Y - x := by rw [hA, hB, Matrix.one_mul, Matrix.mul_one]
    rwa [e2] at h2
  · intro h; rw [e1]; exact ebox_zero_add (hpres _ h) hx'

theorem add_mul_tv {m l : ℕ} (P : Matrix (Fin m) (Fin l) k) (w : Fin m → k) (s : Fin l → k) (j₀ : Fin l)
    (hs0 : s j₀ = 0) : (P + vecMulVec w (Pi.single j₀ 1)) * (1 + vecMulVec (-s) (Pi.single j₀ 1)) =
      P + vecMulVec (w - P *ᵥ s) (Pi.single j₀ 1) := by
  rw [Matrix.mul_add, Matrix.mul_one, mul_vecMulVec, Matrix.add_mulVec, vecMulVec_mulVec]
  have : (Pi.single j₀ (1 : k) : Fin l → k) ⬝ᵥ -s = 0 := by simp [hs0]
  rw [this]
  ext i j; simp [vecMulVec_apply, mulVec_neg]; ring

theorem tv_mul_add {m l : ℕ} (P : Matrix (Fin m) (Fin l) k) (c : Fin m → k) (e : Fin l → k) (i₀ : Fin m)
    (hc0 : c i₀ = 0) (hrow : P.row i₀ = e) : (1 + vecMulVec (-c) (Pi.single i₀ 1)) * (P + vecMulVec c e) = P := by
  rw [Matrix.add_mul, Matrix.one_mul, vecMulVec_mul, Matrix.vecMul_add, single_one_vecMul, vecMul_vecMulVec, hrow]
  have : (Pi.single i₀ (1 : k) : Fin m → k) ⬝ᵥ c = 0 := by simp [hc0]
  rw [this]
  ext i j; simp [vecMulVec_apply]

end GlobalTheory.NormalCore.UnipMove

namespace GlobalTheory.NormalCore.UnipMove

theorem rK1_bounds {n d : ℕ} (i₀ : Fin n) (j₀ : Fin d) (N : ℕ) :
    ∀ i j, N ≤ baseCellRadiiAtEntry i₀ j₀ N i j ∧ baseCellRadiiAtEntry i₀ j₀ N i j ≤ N + 1 := fun i j => by
  unfold baseCellRadiiAtEntry; split_ifs <;> omega

theorem rK2_bounds {n d : ℕ} (j₀ : Fin d) (N : ℕ) :
    ∀ (i : Fin n) j, N ≤ baseCellRadiiAtColumn j₀ N i j ∧ baseCellRadiiAtColumn j₀ N i j ≤ N + 1 := fun i j => by
  unfold baseCellRadiiAtColumn; split_ifs <;> omega

theorem exists_unip_move : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (i₀ : Fin n) (j₀ : Fin d) (ϖ : kˣ), IsUnif ϖ → ∀ (p₁ p₂ : Matrix (Fin n) (Fin d) k) (N : ℕ), 1 ≤ N → (∀ i j, valuation k (p₁ i j) ≤ 1) → (∀ j, p₁ i₀ j = if j = j₀ then 1 else 0) → (∀ i, i ≠ i₀ → p₁ i j₀ = 0) → (∀ i, p₂ i j₀ = 0) → (∃ S : Matrix (Fin d) (Fin n) k, (∀ j i, valuation k (S j i) ≤ 1) ∧ (∀ i, S j₀ i = 0) ∧ p₂ * S = 1) → ∀ x₁ ∈ box ϖ p₁ (fun _ => N), ∀ x₂ ∈ box ϖ p₂ (fun _ => N), ∃ (g : GL (Fin n) k) (h : GL (Fin d) k), gdet g = 1 ∧ {Y : Matrix (Fin n) (Fin d) k | (g.1)ᵀ * Y * h.1 ∈ ebox ϖ p₁ (baseCellRadiiAtEntry i₀ j₀ N)} = ebox ϖ x₁ (baseCellRadiiAtEntry i₀ j₀ N) ∧ {Y : Matrix (Fin n) (Fin d) k | Y * h.1 ∈ ebox ϖ p₂ (baseCellRadiiAtColumn j₀ N)} = ebox ϖ x₂ (baseCellRadiiAtColumn j₀ N) := by
  intro k _ _ _ _ n d i₀ j₀ ϖ hϖ p₁ p₂ N hN hp₁ hrow hcol hp₂ hS x₁ hx₁ x₂ hx₂
  obtain ⟨S, hSi, hS0, hpS⟩ := hS
  set VN := valuation k ((ϖ ^ N : kˣ) : k) with hVN

  set v : Fin n → k := fun i => x₂ i j₀ with hv_def
  set s : Fin d → k := S *ᵥ v with hs_def
  have hs0 : s j₀ = 0 := by simp [s, mulVec, dotProduct, hS0]
  have hps : p₂ *ᵥ s = v := by simp [s, mulVec_mulVec, hpS]
  have hv : ∀ i, valuation k (v i) ≤ VN := fun i => by simpa [v, hp₂, VN] using hx₂ i j₀
  have hsN : ∀ j, valuation k (s j) ≤ VN := fun j => by
    simp only [s, mulVec, dotProduct]
    exact Valuation.map_sum_le _ fun i _ => val_int_mul (hSi j i) (hv i)

  set w : Fin n → k := fun i => if i = i₀ then 0 else x₁ i j₀ with hw_def
  set c : Fin n → k := w - p₁ *ᵥ s with hc_def
  have hc0 : c i₀ = 0 := by
    simp [c, w, mulVec, dotProduct, hrow, hs0]
  have hwN : ∀ i, valuation k (w i) ≤ VN := fun i => by
    by_cases hi : i = i₀
    · simp [w, hi]
    · simpa [w, hi, hcol i hi, VN] using hx₁ i j₀
  have hcN : ∀ i, valuation k (c i) ≤ VN := fun i => by
    refine Valuation.map_sub_le _ (hwN i) ?_
    simp only [mulVec, dotProduct]
    exact Valuation.map_sum_le _ fun j _ => val_int_mul (hp₁ i j) (hsN j)
  have hnegs : ∀ j, valuation k ((-s) j) ≤ VN := fun j => by simpa using hsN j
  have hnegc : ∀ i, valuation k ((-c) i) ≤ VN := fun i => by simpa using hcN i

  set e₁ : Fin n → k := Pi.single i₀ 1 with he₁
  set e₂ : Fin d → k := Pi.single j₀ 1 with he₂
  have hd2 : e₂ ⬝ᵥ (-s) = 0 := by simp [e₂, hs0]
  have hd1 : e₁ ⬝ᵥ (-c) = 0 := by simp [e₁, hc0]
  have hgT' : (1 + vecMulVec c e₁) * (1 + vecMulVec (-c) e₁) = 1 := by
    simpa using tv_neg_mul_tv (-c) e₁ hd1
  have hgT'' : (1 + vecMulVec (-c) e₁) * (1 + vecMulVec c e₁) = 1 := by
    simpa using tv_mul_tv_neg (-c) e₁ hd1
  let h : GL (Fin d) k := ⟨1 + vecMulVec (-s) e₂, 1 + vecMulVec s e₂,
    by simpa using tv_mul_tv_neg (-s) e₂ hd2, by simpa using tv_neg_mul_tv (-s) e₂ hd2⟩
  let g : GL (Fin n) k := ⟨(1 + vecMulVec (-c) e₁)ᵀ, (1 + vecMulVec c e₁)ᵀ,
    by rw [← transpose_mul, hgT', transpose_one], by rw [← transpose_mul, hgT'', transpose_one]⟩
  have hgT : (g.1)ᵀ = 1 + vecMulVec (-c) e₁ := transpose_transpose _
  have hhh : (1 + vecMulVec (-s) e₂) * (1 + vecMulVec s e₂) = 1 := by
    simpa using tv_mul_tv_neg (-s) e₂ hd2
  refine ⟨g, h, ?_, ?_, ?_⟩
  · ext
    simp only [gdet, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    show ((1 + vecMulVec (-c) e₁)ᵀ).det = 1
    rw [det_transpose, Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow, hd1, add_zero]
  · rw [hgT]
    refine preimage_ebox_eq (A' := 1 + vecMulVec c e₁) (B' := 1 + vecMulVec s e₂) (q := p₁ + vecMulVec w e₂)
      hgT' hhh (fun δ hδ => ?_) (fun δ hδ => ?_) ?_ ?_
    · exact mul_tv_mem hϖ hN (rK1_bounds i₀ j₀ N) hnegs j₀ (tv_mul_mem hϖ hN (rK1_bounds i₀ j₀ N) hnegc i₀ hδ)
    · exact mul_tv_mem hϖ hN (rK1_bounds i₀ j₀ N) hsN j₀ (tv_mul_mem hϖ hN (rK1_bounds i₀ j₀ N) hcN i₀ hδ)
    · show (1 + vecMulVec (-c) e₁) * (p₁ + vecMulVec w e₂) * (1 + vecMulVec (-s) e₂) = p₁
      rw [Matrix.mul_assoc, add_mul_tv p₁ w s j₀ hs0]
      exact tv_mul_add p₁ c e₂ i₀ hc0 (funext fun j => by simp [e₂, hrow, Pi.single_apply])
    · rw [mem_ebox_zero]
      intro i j
      have hx := hx₁ i j
      simp only [baseCellRadiiAtEntry]
      by_cases hj : j = j₀
      · subst hj
        by_cases hi : i = i₀
        · subst hi; simpa [w, e₂, vecMulVec_apply] using hx
        · simp [w, e₂, hi, hcol i hi, vecMulVec_apply]
      · simpa [e₂, hj, vecMulVec_apply, Pi.single_apply] using hx
  · have := preimage_ebox_eq (A := 1) (A' := 1) (B := 1 + vecMulVec (-s) e₂) (B' := 1 + vecMulVec s e₂)
      (r := baseCellRadiiAtColumn j₀ N) (p := p₂) (q := p₂ + vecMulVec v e₂) (x := x₂) (Matrix.one_mul 1) hhh
      (fun δ hδ => by simpa using mul_tv_mem hϖ hN (rK2_bounds j₀ N) hnegs j₀ hδ)
      (fun δ hδ => by simpa using mul_tv_mem hϖ hN (rK2_bounds j₀ N) hsN j₀ hδ) ?_ ?_
    · simp only [Matrix.one_mul] at this; exact this
    · rw [Matrix.one_mul, add_mul_tv p₂ v s j₀ hs0, hps, sub_self]
      ext i j; simp [vecMulVec_apply]
    · rw [mem_ebox_zero]
      intro i j
      have hx := hx₂ i j
      simp only [baseCellRadiiAtColumn]
      by_cases hj : j = j₀
      · subst hj; simp [v, e₂, hp₂, vecMulVec_apply]
      · simpa [e₂, hj, vecMulVec_apply, Pi.single_apply] using hx

end GlobalTheory.NormalCore.UnipMove
