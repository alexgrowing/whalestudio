import Mathlib

noncomputable section

open Matrix

namespace GlobalTheory.SingleBlock

variable {k : Type} [Field k] {r t : ℕ}

theorem fromBlocks_mul_inv (p : GL (Fin r) k) (b : Matrix (Fin r) (Fin t) k) (d : GL (Fin t) k) :
    fromBlocks (p : Matrix (Fin r) (Fin r) k) b 0 (d : Matrix (Fin t) (Fin t) k) *
      fromBlocks ((p⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k)
        (-(((p⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * b *
          ((d⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k))) 0
        ((d⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k) = 1 := by
  rw [fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
    ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, neg_add_cancel, neg_zero, fromBlocks_one]

def blockUnit (p : GL (Fin r) k) (b : Matrix (Fin r) (Fin t) k) (d : GL (Fin t) k) :
    GL (Fin r ⊕ Fin t) k :=
  ⟨_, _, fromBlocks_mul_inv p b d, mul_eq_one_comm.1 (fromBlocks_mul_inv p b d)⟩

def blockPar (t : ℕ) (Q : Subgroup (GL (Fin r) k)) : Subgroup (GL (Fin r ⊕ Fin t) k) where
  carrier := {h | ∃ p ∈ Q, ∃ (b : Matrix (Fin r) (Fin t) k) (d : GL (Fin t) k),
    (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k) =
      fromBlocks (p : Matrix (Fin r) (Fin r) k) b 0 (d : Matrix (Fin t) (Fin t) k)}
  one_mem' := ⟨1, Q.one_mem, 0, 1, by simp⟩
  mul_mem' := by
    rintro x y ⟨p, hp, b, d, e⟩ ⟨p', hp', b', d', e'⟩
    refine ⟨p * p', Q.mul_mem hp hp', (p : Matrix (Fin r) (Fin r) k) * b' +
      b * (d' : Matrix (Fin t) (Fin t) k), d * d', ?_⟩
    rw [Units.val_mul, e, e', fromBlocks_multiply]
    simp
  inv_mem' := by
    rintro x ⟨p, hp, b, d, e⟩
    exact ⟨p⁻¹, Q.inv_mem hp, _, d⁻¹,
      Units.inv_eq_of_mul_eq_one_right (e ▸ fromBlocks_mul_inv p b d)⟩

private theorem mem_blockPar_iff' (Q : Subgroup (GL (Fin r) k)) (h : GL (Fin r ⊕ Fin t) k) :
    h ∈ blockPar t Q ↔ ∃ p ∈ Q, ∃ (b : Matrix (Fin r) (Fin t) k) (d : GL (Fin t) k),
      (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k) =
        fromBlocks (p : Matrix (Fin r) (Fin r) k) b 0 (d : Matrix (Fin t) (Fin t) k) :=
  Iff.rfl

theorem mem_blockPar_iff (Q : Subgroup (GL (Fin r) k)) (h : GL (Fin r ⊕ Fin t) k) :
    h ∈ blockPar t Q ↔
      (∃ p ∈ Q, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k).toBlocks₁₁ =
        (p : Matrix (Fin r) (Fin r) k)) ∧
      (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k).toBlocks₂₁ = 0 := by
  rw [mem_blockPar_iff']
  constructor
  · rintro ⟨p, hp, b, d, e⟩
    exact ⟨⟨p, hp, by rw [e, toBlocks_fromBlocks₁₁]⟩, by rw [e, toBlocks_fromBlocks₂₁]⟩
  · rintro ⟨⟨p, hp, h11⟩, h21⟩
    have hM : (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k) =
        fromBlocks (p : Matrix (Fin r) (Fin r) k)
          (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k).toBlocks₁₂ 0
          (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k).toBlocks₂₂ := by
      rw [← h11, ← h21, fromBlocks_toBlocks]
    have hdet : (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k).toBlocks₂₂.det ≠ 0 := by
      intro h0
      have hu := ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit h)).ne_zero
      rw [hM, det_fromBlocks_zero₂₁, h0, mul_zero] at hu
      exact hu rfl
    exact ⟨p, hp, _, Matrix.nonsingInvUnit _ (isUnit_iff_ne_zero.mpr hdet), hM⟩

theorem card_blockPar (Q : Subgroup (GL (Fin r) k)) :
    Nat.card (blockPar t Q) =
      Nat.card Q * (Nat.card k ^ (r * t) * Nat.card (GL (Fin t) k)) := by
  let φ : Q × (Matrix (Fin r) (Fin t) k × GL (Fin t) k) → blockPar t Q := fun x =>
    ⟨blockUnit x.1.1 x.2.1 x.2.2, (mem_blockPar_iff' Q _).mpr ⟨x.1.1, x.1.2, x.2.1, x.2.2, rfl⟩⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨⟨p, hp⟩, b, d⟩ ⟨⟨p', hp'⟩, b', d'⟩ h
      have h1 : fromBlocks (p : Matrix (Fin r) (Fin r) k) b 0 (d : Matrix (Fin t) (Fin t) k) =
          fromBlocks (p' : Matrix (Fin r) (Fin r) k) b' 0 (d' : Matrix (Fin t) (Fin t) k) :=
        congrArg (fun z : blockPar t Q =>
          ((z : GL (Fin r ⊕ Fin t) k) : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k)) h
      obtain ⟨e1, e2, -, e4⟩ := Matrix.fromBlocks_inj.mp h1
      have hp_eq : p = p' := Units.ext e1
      have hd_eq : d = d' := Units.ext e4
      subst hp_eq hd_eq e2
      rfl
    · rintro ⟨h, hh⟩
      obtain ⟨p, hp, b, d, e⟩ := (mem_blockPar_iff' Q h).mp hh
      exact ⟨(⟨p, hp⟩, b, d), Subtype.ext (Units.ext e.symm)⟩
  have hM : Nat.card (Matrix (Fin r) (Fin t) k) = Nat.card k ^ (r * t) := by
    show Nat.card (Fin r → Fin t → k) = _
    rw [Nat.card_fun, Nat.card_fun]
    simp only [Nat.card_eq_fintype_card (α := Fin t), Nat.card_eq_fintype_card (α := Fin r),
      Fintype.card_fin]
    rw [← pow_mul, Nat.mul_comm t r]
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_prod, Nat.card_prod, hM]

theorem card_GL_real [Finite k] (n : ℕ) :
    (Nat.card (GL (Fin n) k) : ℝ) = (Nat.card k : ℝ) ^ (n * n) *
      ∏ i ∈ Finset.Ioc 0 n, (1 - ((Nat.card k : ℝ) ^ i)⁻¹) := by
  classical
  have := Fintype.ofFinite k
  have hq1 : 1 < Nat.card k := Finite.one_lt_card
  have hq : (0 : ℝ) < Nat.card k := Nat.cast_pos.mpr (by omega)
  rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, Nat.cast_prod,
    Fin.prod_univ_eq_prod_range (fun i => ((Nat.card k ^ n - Nat.card k ^ i : ℕ) : ℝ)) n]
  have step : ∀ i ∈ Finset.range n, ((Nat.card k ^ n - Nat.card k ^ i : ℕ) : ℝ) =
      (Nat.card k : ℝ) ^ n * (1 - ((Nat.card k : ℝ) ^ (n - i))⁻¹) := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    rw [Nat.cast_sub (Nat.pow_le_pow_right (by omega) hin.le)]
    push_cast
    have hsplit : (Nat.card k : ℝ) ^ n = (Nat.card k : ℝ) ^ i * (Nat.card k : ℝ) ^ (n - i) := by
      rw [← pow_add]
      congr 1
      omega
    have h2 : (Nat.card k : ℝ) ^ n * ((Nat.card k : ℝ) ^ (n - i))⁻¹ = (Nat.card k : ℝ) ^ i := by
      rw [hsplit, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq.ne'), mul_one]
    rw [mul_sub, mul_one, h2]
  rw [Finset.prod_congr rfl step, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    ← pow_mul]
  congr 1
  apply Finset.prod_nbij' (fun i => n - i) (fun i => n - i)
  · intro a ha
    simp only [Finset.mem_range, Finset.mem_Ioc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_range, Finset.mem_Ioc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    omega
  · intro a ha
    simp only [Finset.mem_Ioc] at ha
    omega
  · intro a _
    rfl

theorem card_GL_sum : Nat.card (GL (Fin r ⊕ Fin t) k) = Nat.card (GL (Fin (r + t)) k) :=
  Nat.card_congr
    (Units.mapEquiv (Matrix.reindexAlgEquiv k k finSumFinEquiv).toRingEquiv.toMulEquiv).toEquiv

private theorem mul_inv_eq_of_mul_eq_mul {I A a b c P P' : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hP : P ≠ 0) (h : I * (A * (b * (c * P))) = a * b * b * c * (P * P')) :
    I * (A * a⁻¹ * b⁻¹) = P' := by
  have key : I * A = a * b * P' := by
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hb hc) hP)
    linear_combination h
  calc I * (A * a⁻¹ * b⁻¹) = (I * A) * (a⁻¹ * b⁻¹) := by ring
    _ = P' * (a * a⁻¹) * (b * b⁻¹) := by rw [key]; ring
    _ = P' := by rw [mul_inv_cancel₀ ha, mul_inv_cancel₀ hb, mul_one, mul_one]

theorem index_blockPar [Finite k] (Q : Subgroup (GL (Fin r) k)) :
    ((blockPar t Q).index : ℝ) * ((Nat.card Q : ℝ) * ((Nat.card k : ℝ) ^ (r ^ 2))⁻¹ *
      ((Nat.card k : ℝ) ^ (r * t))⁻¹) =
      ∏ i ∈ Finset.Ioc t (r + t), (1 - ((Nat.card k : ℝ) ^ i)⁻¹) := by
  have hq1 : 1 < Nat.card k := Finite.one_lt_card
  have hq : (0 : ℝ) < Nat.card k := Nat.cast_pos.mpr (by omega)
  have hq' : (1 : ℝ) < Nat.card k := by exact_mod_cast hq1
  have hpos : ∀ m : ℕ, 0 < ∏ i ∈ Finset.Ioc 0 m, (1 - ((Nat.card k : ℝ) ^ i)⁻¹) := by
    intro m
    apply Finset.prod_pos
    intro i hi
    have hi0 : i ≠ 0 := by
      simp only [Finset.mem_Ioc] at hi
      omega
    have : ((Nat.card k : ℝ) ^ i)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq' hi0)
    linarith
  have hidx := (blockPar t Q).index_mul_card
  rw [card_blockPar, card_GL_sum] at hidx
  have hR : ((blockPar t Q).index : ℝ) * ((Nat.card Q : ℝ) * ((Nat.card k : ℝ) ^ (r * t) *
      (Nat.card (GL (Fin t) k) : ℝ))) = (Nat.card (GL (Fin (r + t)) k) : ℝ) := by
    exact_mod_cast hidx
  rw [card_GL_real, card_GL_real,
    ← Finset.prod_Ioc_consecutive _ (Nat.zero_le t) (Nat.le_add_left t r)] at hR
  have he : (Nat.card k : ℝ) ^ ((r + t) * (r + t)) = (Nat.card k : ℝ) ^ (r ^ 2) *
      (Nat.card k : ℝ) ^ (r * t) * (Nat.card k : ℝ) ^ (r * t) * (Nat.card k : ℝ) ^ (t * t) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    ring
  rw [he] at hR
  exact mul_inv_eq_of_mul_eq_mul (pow_pos hq _).ne' (pow_pos hq _).ne' (pow_pos hq _).ne' (hpos t).ne' hR

end GlobalTheory.SingleBlock
