import Development.AutomorphicSpectrum.Definitions.TwistedFlags.BlockDoubleCosetFunctionsExist

noncomputable section

open Matrix IsDedekindDomain NumberField
open GlobalTheory.CompanionTheory.QL (bAA bAD bDA bDD chi0 pEl)
open GlobalTheory.CompanionTheory.Ipf.Val

namespace CompanionTheory.D.Upq.DoubleCosetLemmas

namespace Sp

section Gen

variable {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (w : Valuation F Γ)

def ParMem (r : ℕ) {n : ℕ} (k : GL (Fin n) F) : Prop :=
  (∀ i j, w (k.1 i j) ≤ 1) ∧ (∀ i j, w ((k⁻¹).1 i j) ≤ 1) ∧
    ∀ i j : Fin n, r ≤ i → (j : ℕ) < r → w (k.1 i j) < 1

def Iso {m n : ℕ} (z : Matrix (Fin m) (Fin n) F) (i : Fin m) (j : Fin n) : Prop :=
  z i j ≠ 0 ∧ (∀ j', j' ≠ j → z i j' = 0) ∧ ∀ i', i' ≠ i → z i' j = 0

def unip {n : ℕ} (N : Matrix (Fin n) (Fin n) F) (h : N * N = 0) : GL (Fin n) F :=
  ⟨1 + N, 1 - N, by rw [add_mul, mul_sub, mul_sub, h]; simp,
    by rw [sub_mul, mul_add, mul_add, h]; simp⟩

variable {w} in
theorem parMem_unip {r n : ℕ} {N : Matrix (Fin n) (Fin n) F} (h : N * N = 0)
    (h1 : ∀ i j, w (N i j) ≤ 1) (h2 : ∀ i j : Fin n, r ≤ i → (j : ℕ) < r → w (N i j) < 1) :
    ParMem w r (unip N h) := by
  have one : ∀ i j : Fin n, w ((1 : Matrix (Fin n) (Fin n) F) i j) ≤ 1 := fun i j => by
    rw [Matrix.one_apply]; split_ifs <;> simp
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j hi hj => ?_⟩
  · exact w.map_add_le (one i j) (h1 i j)
  · exact w.map_sub_le (one i j) (h1 i j)
  · have : i ≠ j := by rintro rfl; omega
    change w ((1 + N) i j) < 1
    rw [Matrix.add_apply, Matrix.one_apply_ne this, zero_add]
    exact h2 i j hi hj

theorem step {r m n : ℕ} (z : Matrix (Fin m) (Fin n) F) (i₁ : Fin m) (j₁ : Fin n)
    (h1 : z i₁ j₁ ≠ 0) (hn : ¬ ∃ j, Iso z i₁ j) :
    ∃ (k' : GL (Fin m) F) (k : GL (Fin n) F), ParMem w r k' ∧ ParMem w r k ∧
      (∀ i j, Iso z i j → Iso (k'.1 * z * k.1) i j) ∧
      ∃ i₀ j₀, (¬ ∃ j, Iso z i₀ j) ∧ Iso (k'.1 * z * k.1) i₀ j₀ := by
  classical
  let f : Fin m × Fin n → Lex (Γ × ℕ) := fun p =>
    toLex (w (z p.1 p.2), (if r ≤ (p.1 : ℕ) then 1 else 0) + if (p.2 : ℕ) < r then 1 else 0)
  obtain ⟨⟨i₀, j₀⟩, hm, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun p : Fin m × Fin n => ¬ ∃ j, Iso z p.1 j) f ⟨(i₁, j₁), by simpa using hn⟩
  have hm0 : ¬ ∃ j, Iso z i₀ j := by simpa using hm
  have hle : ∀ i j, (¬ ∃ j, Iso z i j) → w (z i j) < w (z i₀ j₀) ∨ (w (z i j) = w (z i₀ j₀) ∧
      ((if r ≤ (i : ℕ) then 1 else 0) + if (j : ℕ) < r then 1 else 0) ≤
        (if r ≤ (i₀ : ℕ) then 1 else 0) + if (j₀ : ℕ) < r then 1 else 0) := fun i j h => by
    have := hmax (i, j) (by simpa using h)
    exact Prod.Lex.toLex_le_toLex.1 this
  have hp : z i₀ j₀ ≠ 0 := by
    intro h0
    have : 0 < w (z i₁ j₁) := zero_lt_iff.2 (w.ne_zero_iff.2 h1)
    rcases hle i₁ j₁ hn with h | h
    · rw [h0, map_zero] at h; exact absurd h not_lt_zero'
    · rw [h0, map_zero] at h; exact this.ne' h.1
  have hwp : 0 < w (z i₀ j₀) := zero_lt_iff.2 (w.ne_zero_iff.2 hp)
  have hcol : ∀ i j, Iso z i j → z i j₀ = 0 := fun i j h => by
    refine h.2.1 j₀ ?_
    rintro rfl
    by_cases e : i₀ = i
    · exact hm0 ⟨_, e ▸ h⟩
    · exact hp (h.2.2 i₀ e)
  let a : Fin m → F := fun i => if i = i₀ then 0 else -(z i j₀ / z i₀ j₀)
  let b : Fin n → F := fun j => if j = j₀ then 0 else -(z i₀ j / z i₀ j₀)
  let N' : Matrix (Fin m) (Fin m) F := Matrix.of fun i l => if l = i₀ then a i else 0
  let N : Matrix (Fin n) (Fin n) F := Matrix.of fun l j => if l = j₀ then b j else 0
  have hN' : N' * N' = 0 := by
    ext i l
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : x = i₀ <;> simp [N', a, hx]
  have hN : N * N = 0 := by
    ext i l; simp [N, Matrix.mul_apply, b]
  have hent : ∀ i j, ((unip N' hN').1 * z * (unip N hN).1) i j =
      (z i j + a i * z i₀ j) + (z i j₀ + a i * z i₀ j₀) * b j := fun i j => by
    have e1 : ∀ j, ((1 + N') * z : Matrix (Fin m) (Fin n) F) i j = z i j + a i * z i₀ j := fun j => by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply]
      simp [N']
    change ((1 + N') * z * (1 + N) : Matrix (Fin m) (Fin n) F) i j = _
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, e1, Matrix.mul_apply]
    simp only [N, Matrix.of_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, e1]
  have hq : ∀ x : F, w x ≤ w (z i₀ j₀) → w (-(x / z i₀ j₀)) ≤ 1 := fun x h => by
    rw [Valuation.map_neg, map_div₀]; exact div_le_one_of_le₀ h zero_le'
  have hq' : ∀ x : F, w x < w (z i₀ j₀) → w (-(x / z i₀ j₀)) < 1 := fun x h => by
    rw [Valuation.map_neg, map_div₀]; exact (div_lt_one₀ hwp).2 h
  refine ⟨unip N' hN', unip N hN, parMem_unip _ (fun i l => ?_) (fun i l hi hl => ?_),
    parMem_unip _ (fun l j => ?_) (fun l j hl hj => ?_), fun i j h => ?_, i₀, j₀, hm0, ?_⟩
  · simp only [N', a, Matrix.of_apply]
    split_ifs
    · simp
    · refine hq _ ?_
      by_cases hi : ∃ j, Iso z i j
      · obtain ⟨j, hj⟩ := hi; simp [hcol i j hj]
      · rcases hle i j₀ hi with h | h
        exacts [h.le, h.1.le]
    · simp
  · simp only [N', a, Matrix.of_apply]
    split_ifs with e1 e2
    · simp
    · refine hq' _ ?_
      subst e1
      by_cases hi' : ∃ j, Iso z i j
      · obtain ⟨j, hj⟩ := hi'; simpa [hcol i j hj] using hwp
      · rcases hle i j₀ hi' with h | h
        · exact h
        · have := h.2
          rw [if_pos hi, if_neg (by omega : ¬ r ≤ (l : ℕ))] at this
          omega
    · simp
  · simp only [N, b, Matrix.of_apply]
    split_ifs
    · simp
    · refine hq _ ?_
      rcases hle i₀ j hm0 with h | h
      exacts [h.le, h.1.le]
    · simp
  · simp only [N, b, Matrix.of_apply]
    split_ifs with e1 e2
    · simp
    · refine hq' _ ?_
      subst e1
      rcases hle i₀ j hm0 with h | h
      · exact h
      · have := h.2
        rw [if_pos hj, if_neg (by omega : ¬ (l : ℕ) < r)] at this
        omega
    · simp
  · have hi : i ≠ i₀ := by rintro rfl; exact hm0 ⟨j, h⟩
    have h0 := hcol i j h
    have hj : j ≠ j₀ := by rintro rfl; exact h.1 h0
    have h0' : z i₀ j = 0 := h.2.2 i₀ hi.symm
    have ha : a i = 0 := by simp [a, h0]
    have hb : b j = 0 := by simp [b, h0']
    refine ⟨?_, fun j' hj' => ?_, fun i' hi' => ?_⟩
    · rw [hent, ha, hb]; simpa using h.1
    · rw [hent, ha, h0, h.2.1 j' hj']; simp
    · rw [hent, hb, h0', h.2.2 i' hi']; simp
  · refine ⟨?_, fun j' hj' => ?_, fun i' hi' => ?_⟩
    · rw [hent]; simpa [a, b] using hp
    · rw [hent]; simp only [a, b, if_true, if_neg hj']; field_simp; ring
    · rw [hent]; simp only [a, b, if_true, if_neg hi']; field_simp; ring

def dg {n : ℕ} (i : Fin n) (u : Fˣ) : GL (Fin n) F :=
  ⟨diagonal (Function.update 1 i (u : F)), diagonal (Function.update 1 i ((u⁻¹ : Fˣ) : F)),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext l; by_cases h : l = i <;> simp [h],
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext l; by_cases h : l = i <;> simp [h]⟩

end Gen

end Sp

end CompanionTheory.D.Upq.DoubleCosetLemmas

end
