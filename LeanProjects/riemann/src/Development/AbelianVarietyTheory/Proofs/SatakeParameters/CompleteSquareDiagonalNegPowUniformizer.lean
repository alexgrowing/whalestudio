import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalThetaPairExistence
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulSelfEqOneIffOfLinearOrderedCommGroupWithZero

noncomputable section

open Matrix

namespace GlobalTheory.Hk3.SquareDiag

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n' : ℕ}

def selE (a : Fin n' → ℕ) (n : ℕ) : Matrix (Fin n') (Fin n) L :=
  Matrix.of fun i p => if (i : ℕ) = (p : ℕ) ∧ 0 < a i then 1 else 0

def halfSel (a : Fin n' → ℕ) (i j : Fin n') : L :=
  if a i < a j ∨ (a i = a j ∧ (i : ℕ) < (j : ℕ)) then 1 else if (i : ℕ) = (j : ℕ) then 2⁻¹ else 0

theorem diag_sel (ϖ : L) (a : Fin n' → ℕ) (n : ℕ) :
    (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) =
      (diagonal (fun i : Fin n' => ϖ⁻¹ ^ a i) : Matrix (Fin n') (Fin n') L) * (selE a n : Matrix (Fin n') (Fin n) L) := by
  ext i j
  simp only [Matrix.diagonal_mul, selE, Matrix.of_apply]
  split_ifs <;> simp

theorem selE_mul_transpose (a : Fin n' → ℕ) (n : ℕ) :
    (selE (L := L) a n : Matrix (Fin n') (Fin n) L) * (selE a n : Matrix (Fin n') (Fin n) L)ᵀ = diagonal (fun i : Fin n' => if (i : ℕ) < n ∧ 0 < a i then (1 : L) else 0) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  simp only [selE, Matrix.of_apply, Matrix.transpose_apply]
  by_cases h : (i : ℕ) < n ∧ 0 < a i
  · rw [Finset.sum_eq_single (⟨i, h.1⟩ : Fin n)]
    · by_cases hij : i = j
      · subst hij; simp [h]
      · have : (j : ℕ) ≠ (i : ℕ) := fun e => hij (Fin.ext e.symm)
        simp [hij, this]
    · intro b _ hb
      have : (i : ℕ) ≠ (b : ℕ) := fun e => hb (Fin.ext e.symm)
      simp [this]
    · intro hn; exact absurd (Finset.mem_univ _) hn
  · rw [if_neg h, ite_self]
    refine Finset.sum_eq_zero fun p _ => ?_
    have : ¬ ((i : ℕ) = (p : ℕ) ∧ 0 < a i) := fun ⟨e, ha⟩ => h ⟨e ▸ p.isLt, ha⟩
    rw [if_neg this, zero_mul]

theorem halfSel_add (h2 : (2 : L) ≠ 0) (a : Fin n' → ℕ) (i j : Fin n') :
    halfSel (L := L) a i j + halfSel a j i = 1 := by
  unfold halfSel
  rcases eq_or_ne i j with rfl | hne
  · simp only [lt_irrefl, false_or, and_false, if_false, if_true]
    rw [← two_mul, mul_inv_cancel₀ h2]
  have hne' : (i : ℕ) ≠ (j : ℕ) := Fin.val_ne_of_ne hne
  split_ifs <;> first | (exfalso; omega) | simp | rw [← two_mul, mul_inv_cancel₀ h2]

end GlobalTheory.Hk3.SquareDiag

namespace GlobalTheory.Hk3.SquareDiag

set_option maxHeartbeats 1000000 in
open GlobalTheory.Hk3 in

theorem square_diag : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (A B : Matrix (Fin n) (Fin n) L) (ψ : AddChar L ℂ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → (∀ i j, A i j ∈ Formalism.UG.intL L) → (∀ i j, B i j ∈ Formalism.UG.intL L) → A * B = 1 →
    (∀ i j, σ (A i j) = A j i) →
    (Valued.v δ = 1 ∧ σ δ = -δ) → (∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1) →
    (∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) → ∀ a : Fin n' → ℕ,
    (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * ((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) * A * Matrix.transpose (((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))).map σ))) + σ (δ * Matrix.trace (C * ((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) * A * Matrix.transpose (((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))).map σ))))) / 2) = 1) →
    ∃ l ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n,
      ∀ i j, (((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l) * A * Matrix.transpose (((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l).map σ)) i j ∈ Formalism.UG.intL L := by
  intro L _ _ ϖ σ q δ n n' A B ψ hU hq hA hB hAB hherm hδ hψ hne a hC
  classical
  have hσσ := hU.1
  have hσv := hU.2.1
  have hσϖ := hU.2.2.1
  have hvϖ := hU.2.2.2.1
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hq
  have h20 : (2 : L) ≠ 0 := by intro h; rw [h, map_zero] at h2; exact zero_ne_one h2
  have hϖ0 : ϖ ≠ 0 := by intro h; rw [h, map_zero] at hvϖ; exact WithZero.zero_ne_coe hvϖ
  have hϖlt : Valued.v ϖ < 1 := by rw [hvϖ]; decide
  have hϖi : ϖ ∈ Formalism.UG.intL L := le_of_lt hϖlt
  have hδi : δ ∈ Formalism.UG.intL L := le_of_eq hδ.1
  have hσi : ∀ x ∈ Formalism.UG.intL L, σ x ∈ Formalism.UG.intL L := fun x hx => by
    show Valued.v (σ x) ≤ 1; rw [hσv]; exact hx
  have hσpow : ∀ k : ℕ, σ (ϖ⁻¹ ^ k) = ϖ⁻¹ ^ k := fun k => by rw [map_pow, map_inv₀, hσϖ]
  set D : Matrix (Fin n') (Fin n) L := Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0) with hDdef
  set E : Matrix (Fin n') (Fin n) L := selE a n with hEdef
  set Δ : Matrix (Fin n') (Fin n') L := diagonal (fun i : Fin n' => ϖ⁻¹ ^ a i) with hΔ
  have hDE : D = Δ * E := diag_sel ϖ a n
  have hEσ : E.map σ = E := by
    ext i p; simp only [E, selE, Matrix.map_apply, Matrix.of_apply]; split_ifs <;> simp
  have hΔσ : Δ.map σ = Δ := by
    ext i j; simp only [Δ, Matrix.map_apply, Matrix.diagonal_apply]; split_ifs
    · exact hσpow _
    · exact map_zero σ
  have hDσ : D.map σ = D := by rw [hDE, Matrix.map_mul, hEσ, hΔσ]
  have hAm : A.map σ = Aᵀ := by ext i j; simp [hherm]
  have hAσ : (A.map σ)ᵀ = A := by rw [hAm, Matrix.transpose_transpose]
  have hBA : B * A = 1 := mul_eq_one_comm.mp hAB
  have hBσ : (B.map σ)ᵀ = B := by
    have h1 : (B.map σ)ᵀ * A = 1 := by
      have : ((A * B).map σ)ᵀ = ((1 : Matrix (Fin n) (Fin n) L).map σ)ᵀ := by rw [hAB]
      rwa [Matrix.map_mul, Matrix.transpose_mul, hAσ, Matrix.map_one _ (map_zero σ) (map_one σ),
        Matrix.transpose_one] at this
    calc (B.map σ)ᵀ = (B.map σ)ᵀ * (A * B) := by rw [hAB, Matrix.mul_one]
      _ = B := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hEi : ∀ i p, E i p ∈ Formalism.UG.intL L := by
    intro i p; simp only [E, selE, Matrix.of_apply]; split_ifs
    · exact (Formalism.UG.intL L).one_mem
    · exact (Formalism.UG.intL L).zero_mem
  have hErow : ∀ i : Fin n', ¬ ((i : ℕ) < n ∧ 0 < a i) → ∀ p, E i p = 0 := by
    intro i h p; simp only [E, selE, Matrix.of_apply]
    rw [if_neg]; rintro ⟨e, ha⟩; exact h ⟨e ▸ p.isLt, ha⟩
  set A' : Matrix (Fin n') (Fin n') L := E * A * Eᵀ with hA'def
  have hA'i : ∀ i j, A' i j ∈ Formalism.UG.intL L := fun i j =>
    matMul_int (matMul_int hEi hA) (fun p k => hEi k p) i j
  have hA'σ : ∀ i j, σ (A' i j) = A' j i := by
    have hm : A'.map σ = A'ᵀ := by
      rw [hA'def, Matrix.map_mul, Matrix.map_mul, hEσ, hAm, Matrix.transpose_map, hEσ, Matrix.transpose_mul,
        Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    intro i j
    have := congrFun (congrFun hm i) j
    simpa using this
  set s : Fin n' → L := fun i => if (i : ℕ) < n ∧ 0 < a i then (1 : L) else 0 with hsdef
  have hEE : E * Eᵀ = diagonal s := selE_mul_transpose a n
  have hA's : ∀ i j, A' i j * s i = A' i j ∧ A' i j * s j = A' i j := by
    intro i j
    by_cases hi : (i : ℕ) < n ∧ 0 < a i
    · by_cases hj : (j : ℕ) < n ∧ 0 < a j
      · simp [s, hi, hj]
      · have : A' i j = 0 := by
          simp only [A', Matrix.mul_apply, Matrix.transpose_apply, hErow j hj, mul_zero, Finset.sum_const_zero]
        simp [this]
    · have : A' i j = 0 := by
        simp only [A', Matrix.mul_apply, Matrix.transpose_apply, hErow i hi, zero_mul, Finset.sum_const_zero]
      simp [this]
  set G : Matrix (Fin n') (Fin n') L := D * A * (D.map σ)ᵀ with hGdef
  have hGΔ : G = Δ * A' * Δ := by
    rw [hGdef, hDσ, hDE, Matrix.transpose_mul, hΔ, Matrix.diagonal_transpose, hA'def]
    simp only [Matrix.mul_assoc]
  have hGe : ∀ i j, G i j = ϖ⁻¹ ^ a i * A' i j * ϖ⁻¹ ^ a j := by
    intro i j; rw [hGΔ, hΔ, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hGσ : ∀ i j, σ (G i j) = G j i := by
    intro i j; rw [hGe, hGe, map_mul, map_mul, hσpow, hσpow, hA'σ]; ring

  have hbound : ∀ i j, ϖ ^ (max (max (a i) (a j)) 1) * G j i ∈ Formalism.UG.intL L := by
    intro i j
    set m := max (max (a i) (a j)) 1 with hm
    have hmi : a i ≤ m := by omega
    have hmj : a j ≤ m := by omega
    have hm1 : 1 ≤ m := by omega
    have hsm : ∀ b' ∈ Formalism.UG.intL L, Valued.v (δ * (b' * ϖ ^ m)) < 1 ∧
        ∀ k ≤ m, δ * (b' * ϖ ^ m) * ϖ⁻¹ ^ k ∈ Formalism.UG.intL L := by
      intro b' hb'
      refine ⟨?_, fun k hk => ?_⟩
      · have e : δ * (b' * ϖ ^ m) = (δ * b' * ϖ ^ (m - 1)) * ϖ := by
          rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hm1, mul_assoc]
        have hx : Valued.v (δ * b' * ϖ ^ (m - 1)) ≤ 1 := mul_mem (mul_mem hδi hb') (pow_mem hϖi _)
        rw [e, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' hx) hϖlt
      · have e : δ * (b' * ϖ ^ m) * ϖ⁻¹ ^ k = δ * b' * ϖ ^ (m - k) := by
          rw [← pow_sub_mul_pow ϖ hk, inv_pow]; field_simp
        rw [e]; exact mul_mem (mul_mem hδi hb') (pow_mem hϖi _)
    have hw : δ ^ 2 * ϖ ^ m * G j i ∈ Formalism.UG.intL L := by
      refine int_of_psi hU ψ hne _ (fun b hb => ?_)
      have hσb := hσi b hb
      set x := δ * (b * ϖ ^ m) with hx
      set y := δ * (σ b * ϖ ^ m) with hy
      have hσx : σ x = -y := by rw [hx, hy, map_mul, map_mul, map_pow, hσϖ, hδ.2]; ring
      have hσy : σ y = -x := by rw [hx, hy, map_mul, map_mul, map_pow, hσϖ, hδ.2, hσσ]; ring
      set C : Matrix (Fin n') (Fin n') L := Matrix.single i j x + Matrix.single j i y with hCdef
      have hskew : ∀ k l, σ (C k l) = - C l k := by
        intro k l
        simp only [hCdef, Matrix.add_apply, Matrix.single_apply]
        have e1 : (i = l ∧ j = k) ↔ (j = k ∧ i = l) := and_comm
        have e2 : (j = l ∧ i = k) ↔ (i = k ∧ j = l) := and_comm
        by_cases hP : i = k ∧ j = l <;> by_cases hQ : j = k ∧ i = l
        · rw [if_pos hP, if_pos hQ, if_pos (e1.2 hQ), if_pos (e2.2 hP), map_add, hσx, hσy]; ring
        · rw [if_pos hP, if_neg hQ, if_neg (fun h => hQ (e1.1 h)), if_pos (e2.2 hP), map_add, hσx, map_zero]; ring
        · rw [if_neg hP, if_pos hQ, if_pos (e1.2 hQ), if_neg (fun h => hP (e2.1 h)), map_add, hσy, map_zero]; ring
        · rw [if_neg hP, if_neg hQ, if_neg (fun h => hQ (e1.1 h)), if_neg (fun h => hP (e2.1 h)), map_add, map_zero]; ring
      have hsmall : ∀ k l, Valued.v (C k l) < 1 := by
        intro k l
        simp only [hCdef, Matrix.add_apply, Matrix.single_apply]
        refine Valuation.map_add_lt _ ?_ ?_
        · split_ifs
          · exact (hsm b hb).1
          · rw [map_zero]; exact zero_lt_one
        · split_ifs
          · exact (hsm (σ b) hσb).1
          · rw [map_zero]; exact zero_lt_one
      have hsingle : ∀ (r s' : Fin n') (z : L), (∀ p, z * D s' p ∈ Formalism.UG.intL L) →
          ∀ k p, (Matrix.single r s' z * D) k p ∈ Formalism.UG.intL L := by
        intro r s' z hz k p
        by_cases h : k = r
        · subst h; rw [Matrix.single_mul_apply_same]; exact hz p
        · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ h]; exact (Formalism.UG.intL L).zero_mem
      have hDrow : ∀ (s' : Fin n') (b' : L), b' ∈ Formalism.UG.intL L → a s' ≤ m →
          ∀ p, δ * (b' * ϖ ^ m) * D s' p ∈ Formalism.UG.intL L := by
        intro s' b' hb' hs' p
        rw [hDdef, Matrix.of_apply]
        split_ifs
        · exact (hsm b' hb').2 _ hs'
        · rw [mul_zero]; exact (Formalism.UG.intL L).zero_mem
      have hint : ∀ k p, (C * D) k p ∈ Formalism.UG.intL L := by
        intro k p
        rw [hCdef, Matrix.add_mul, Matrix.add_apply]
        exact add_mem (hsingle i j x (hDrow j b hb hmj) k p) (hsingle j i y (hDrow i (σ b) hσb hmi) k p)
      have h := hC C hskew hsmall hint
      have htr : Matrix.trace (C * G) = x * G j i + y * G i j := by
        rw [hCdef, Matrix.add_mul, Matrix.trace_add, Matrix.trace_single_mul, Matrix.trace_single_mul, smul_eq_mul, smul_eq_mul]
      rw [htr] at h
      have key : (δ * (x * G j i + y * G i j) + σ (δ * (x * G j i + y * G i j))) / 2 =
          b * (δ ^ 2 * ϖ ^ m * G j i) + σ (b * (δ ^ 2 * ϖ ^ m * G j i)) := by
        rw [hx, hy]
        simp only [map_add, map_mul, map_pow, hσϖ, hδ.2, hσσ, hGσ]
        rw [div_eq_iff h20]; ring
      rw [← key]; exact h
    have e : Valued.v (δ ^ 2 * ϖ ^ m * G j i) = Valued.v (ϖ ^ m * G j i) := by
      rw [mul_assoc, map_mul, map_pow, hδ.1, one_pow, one_mul]
    rw [GlobalTheory.Hk3.mem_intL_iff, ← e]; exact hw
  set t : Fin n' → Fin n' → L := halfSel a with htdef
  have ht : ∀ i j, t i j + t j i = 1 := halfSel_add h20 a
  have h2i : (2 : L)⁻¹ ∈ Formalism.UG.intL L := by rw [GlobalTheory.Hk3.mem_intL_iff, map_inv₀, h2, inv_one]
  have htσ : ∀ i j, σ (t i j) = t i j := by
    intro i j; simp only [htdef, halfSel]; split_ifs <;> simp [map_inv₀, map_ofNat]
  have hcore : ∀ i j, a i ≤ a j → ϖ⁻¹ ^ a i * A' i j ∈ Formalism.UG.intL L := by
    intro i j hle
    rcases Nat.eq_zero_or_pos (a i) with h0 | hpos
    · rw [h0, pow_zero, one_mul]; exact hA'i i j
    · have hmx : max (max (a j) (a i)) 1 = a j := by omega
      have := hbound j i
      rw [hmx, hGe i j] at this
      have e : ϖ ^ a j * (ϖ⁻¹ ^ a i * A' i j * ϖ⁻¹ ^ a j) = ϖ⁻¹ ^ a i * A' i j := by
        rw [inv_pow, inv_pow]; field_simp
      rwa [e] at this
  set W : Matrix (Fin n') (Fin n') L := Matrix.of fun i j => t i j * (ϖ⁻¹ ^ a i * A' i j) with hWdef
  have hWi : ∀ i j, W i j ∈ Formalism.UG.intL L := by
    intro i j
    simp only [hWdef, Matrix.of_apply, htdef, halfSel]
    split_ifs with h1 h3
    · exact mul_mem (Formalism.UG.intL L).one_mem (hcore i j (by rcases h1 with h | ⟨h, -⟩ <;> omega))
    · exact mul_mem h2i (hcore i j (le_of_eq (congrArg a (Fin.ext h3))))
    · rw [zero_mul]; exact (Formalism.UG.intL L).zero_mem
  set Z : Matrix (Fin n') (Fin n) L := W * E with hZdef
  set Zσ : Matrix (Fin n) (Fin n') L := (Z.map σ)ᵀ with hZσdef
  have hZi : ∀ i p, Z i p ∈ Formalism.UG.intL L := matMul_int hWi hEi
  have hZσi : ∀ p i, Zσ p i ∈ Formalism.UG.intL L := fun p i => hσi _ (hZi i p)
  have hDZ : D * Zσ = Δ * (diagonal s * (W.map σ)ᵀ) := by
    rw [hDE, hZσdef, hZdef, Matrix.map_mul, Matrix.transpose_mul, hEσ, Matrix.mul_assoc, ← Matrix.mul_assoc E, hEE]
  have hZD : Z * Dᵀ = W * (diagonal s * Δ) := by
    rw [hZdef, hDE, Matrix.transpose_mul, hΔ, Matrix.diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc E, hEE]
  have hsplit : G = D * Zσ + Z * Dᵀ := by
    ext i j
    rw [hGe, Matrix.add_apply, hDZ, hZD, hΔ, Matrix.diagonal_mul, Matrix.diagonal_mul, Matrix.diagonal_mul_diagonal,
      Matrix.mul_diagonal]
    simp only [Matrix.transpose_apply, Matrix.map_apply, hWdef, Matrix.of_apply, map_mul, htσ, hσpow, hA'σ]
    obtain ⟨e1, e2⟩ := hA's i j
    linear_combination (-(ϖ⁻¹ ^ a i * ϖ⁻¹ ^ a j * t j i)) * e1 + (-(ϖ⁻¹ ^ a i * ϖ⁻¹ ^ a j * t i j)) * e2 +
      (-(ϖ⁻¹ ^ a i * ϖ⁻¹ ^ a j * A' i j)) * ht i j
  refine ⟨Z * B, fun i p => matMul_int hZi hB i p, ?_⟩
  have hlσ : ((D - Z * B).map σ)ᵀ = Dᵀ - B * Zσ := by
    rw [hZσdef, Matrix.map_sub _ (map_sub σ), hDσ, Matrix.transpose_sub, Matrix.map_mul, Matrix.transpose_mul, hBσ]
  have hM : (D - Z * B) * A * ((D - Z * B).map σ)ᵀ = Z * B * Zσ := by
    rw [hlσ, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    have e1 : D * A * (B * Zσ) = D * Zσ := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc A, hAB, Matrix.one_mul]
    have e2 : Z * B * A * Dᵀ = Z * Dᵀ := by rw [Matrix.mul_assoc Z, hBA, Matrix.mul_one]
    have e3 : Z * B * A * (B * Zσ) = Z * B * Zσ := by
      calc Z * B * A * (B * Zσ) = Z * (B * A) * (B * Zσ) := by rw [Matrix.mul_assoc Z B A]
        _ = Z * (B * Zσ) := by rw [hBA, Matrix.mul_one]
        _ = Z * B * Zσ := (Matrix.mul_assoc _ _ _).symm
    have e4 : D * A * Dᵀ = G := by rw [hGdef, hDσ]
    rw [e1, e2, e3, e4, hsplit]; abel
  intro i j
  rw [hM]
  exact matMul_int (matMul_int hZi hB) hZσi i j

end GlobalTheory.Hk3.SquareDiag
