import Mathlib
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

open Matrix Formalism.QuantumDeterminants CompanionTheory.Bmu

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuDecomp

section general

variable {n : ℕ}

theorem iso_mul {A B C P Q : Matrix (Fin n) (Fin n) ℂ} (hP : Pᴴ * A * P = B) (hQ : Qᴴ * B * Q = C) :
    (P * Q)ᴴ * A * (P * Q) = C := by
  rw [← hQ, ← hP, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem iso_inv {A B P Q : Matrix (Fin n) (Fin n) ℂ} (hP : Pᴴ * A * P = B) (h : P * Q = 1) :
    Qᴴ * B * Q = A := by
  have := iso_mul hP (rfl : Qᴴ * B * Q = _)
  rw [← this, h]
  simp

theorem iso_exists_inv {A B P : Matrix (Fin n) (Fin n) ℂ} (hP : Pᴴ * A * P = B) (hB : B * B = 1) :
    ∃ Q, P * Q = 1 ∧ Q * P = 1 := by
  have h : (B * Pᴴ * A) * P = 1 := by
    rw [← hB]
    conv_rhs => rw [← hP]
    conv_rhs => enter [1]; rw [hP]
    simp only [Matrix.mul_assoc]
  exact ⟨_, mul_eq_one_comm.mp h, h⟩

theorem uni_mul {P Q : Matrix (Fin n) (Fin n) ℂ} (hP : Pᴴ * P = 1) (hQ : Qᴴ * Q = 1) :
    (P * Q)ᴴ * (P * Q) = 1 := by
  have := iso_mul (A := 1) (B := 1) (C := 1) (P := P) (Q := Q) (by simpa using hP) (by simpa using hQ)
  simpa only [Matrix.mul_one] using this

theorem fix_inv {P Q : Matrix (Fin n) (Fin n) ℂ} (h : Q * P = 1) {v : Fin n → ℂ} (hv : P *ᵥ v = v) :
    Q *ᵥ v = v := by
  conv_lhs => rw [← hv]
  rw [mulVec_mulVec, h, one_mulVec]

theorem fix_mul {P Q : Matrix (Fin n) (Fin n) ℂ} {v : Fin n → ℂ} (hv : P *ᵥ v = v) (hw : Q *ᵥ v = v) :
    (P * Q) *ᵥ v = v := by
  rw [← mulVec_mulVec, hw, hv]

theorem fix_adj {A B P : Matrix (Fin n) (Fin n) ℂ} (hP : Pᴴ * A * P = B) {v w : Fin n → ℂ} (hv : P *ᵥ v = v)
    (hA : A *ᵥ v = w) (hB : B *ᵥ v = w) : Pᴴ *ᵥ w = w := by
  conv_rhs => rw [← hB, ← hP, ← mulVec_mulVec, ← mulVec_mulVec, hv, hA]

theorem col_of_fix {P : Matrix (Fin n) (Fin n) ℂ} {i : Fin n} (h : P *ᵥ bvec i = bvec i) (j : Fin n) :
    P j i = if j = i then 1 else 0 := by
  have := congrFun h j
  simpa [bvec, Pi.single_apply] using this

theorem row_of_fix {P : Matrix (Fin n) (Fin n) ℂ} {i : Fin n} (h : Pᴴ *ᵥ bvec i = bvec i) (j : Fin n) :
    P i j = if j = i then 1 else 0 := by
  have := congrArg star (col_of_fix h j)
  rw [conjTranspose_apply, star_star] at this
  rw [this]
  split_ifs <;> simp

end general

variable {k r : ℕ}

theorem hq_sq : Hq k r * Hq k r = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : outer k r i
  · rw [Finset.sum_eq_single (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))]
    · have h2 : outer k r ⟨2 * r + k - i.val, by omega⟩ := by
        unfold outer at *; have := i.isLt; simp only; omega
      have := i.isLt
      simp only [Hq, hi, h2, if_true, Matrix.one_apply, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · intro b _ hb
      have : ¬ (i.val + b.val = 2 * r + k) := fun h => hb (Fin.ext (by simp only; omega))
      simp [Hq, hi, this]
    · simp
  · rw [Finset.sum_eq_single i]
    · simp [Hq, hi, Matrix.one_apply]
    · intro b _ hb
      simp [Hq, hi, Ne.symm hb]
    · simp

theorem hq_e (a : Fin r) : Hq k r *ᵥ bvec (eI k r a) = bvec (esI k r a) := by
  ext i
  have := a.isLt
  have := i.isLt
  simp only [bvec, mulVec_single_one, Matrix.col_apply, Pi.single_apply, Hq, outer, eI, esI, Fin.ext_iff]
  split_ifs <;> first | omega | rfl

theorem hq_es (a : Fin r) : Hq k r *ᵥ bvec (esI k r a) = bvec (eI k r a) := by
  ext i
  have := a.isLt
  have := i.isLt
  simp only [bvec, mulVec_single_one, Matrix.col_apply, Pi.single_apply, Hq, outer, eI, esI, Fin.ext_iff]
  split_ifs <;> first | omega | rfl

theorem hpk_e (a : Fin r) : Hpk k r *ᵥ bvec (eI k r a) = bvec (esI k r a) := by
  ext i
  have := a.isLt
  have := i.isLt
  simp only [bvec, mulVec_single_one, Matrix.col_apply, Pi.single_apply, Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | omega | rfl

theorem hpk_es (a : Fin r) : Hpk k r *ᵥ bvec (esI k r a) = bvec (eI k r a) := by
  ext i
  have := a.isLt
  have := i.isLt
  simp only [bvec, mulVec_single_one, Matrix.col_apply, Pi.single_apply, Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | omega | rfl

theorem block_of_fix {A B P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hP : Pᴴ * A * P = B)
    (hA : ∀ a : Fin r, A *ᵥ bvec (eI k r a) = bvec (esI k r a) ∧ A *ᵥ bvec (esI k r a) = bvec (eI k r a))
    (hB : ∀ a : Fin r, B *ᵥ bvec (eI k r a) = bvec (esI k r a) ∧ B *ᵥ bvec (esI k r a) = bvec (eI k r a))
    (hf : ∀ a : Fin r, P *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ P *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (i : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    P j i = (if j = i then 1 else 0) ∧ P i j = (if j = i then 1 else 0) := by
  have := i.isLt
  rcases hi with hi | hi
  · have e : i = eI k r ⟨i.val, hi⟩ := rfl
    rw [e]
    exact ⟨col_of_fix (hf _).1 j, row_of_fix (fix_adj hP (hf _).2 (hA _).2 (hB _).2) j⟩
  · have e : i = esI k r ⟨2 * r + k - i.val, by omega⟩ := Fin.ext (by simp only [esI]; omega)
    rw [e]
    exact ⟨col_of_fix (hf _).2 j, row_of_fix (fix_adj hP (hf _).1 (hA _).1 (hB _).1) j⟩

theorem conj_mem_N {P Q m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Pᴴ * Hpk k r * P = Hq k r) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hf : ∀ a : Fin r, P *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ P *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (hm : m ∈ Nq k r) : P * m * Q ∈ Nset k r := by
  have hQ := iso_inv hP hPQ
  have bP := block_of_fix hP (fun a => ⟨hpk_e a, hpk_es a⟩) (fun a => ⟨hq_e a, hq_es a⟩) hf
  have bQ := block_of_fix hQ (fun a => ⟨hq_e a, hq_es a⟩) (fun a => ⟨hpk_e a, hpk_es a⟩)
    (fun a => ⟨fix_inv hQP (hf a).1, fix_inv hQP (hf a).2⟩)
  obtain ⟨hm0, hm1, hm2⟩ := hm
  have key : ∀ i j, (P * m * Q) i j = (if i = j then 1 else 0) + ∑ p, ∑ l, P i l * (m - 1) l p * Q p j := by
    intro i j
    have : P * m * Q = 1 + P * (m - 1) * Q := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ]; abel
    rw [this, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply]
    simp only [Matrix.mul_apply, Finset.sum_mul]
  refine ⟨iso_mul (iso_mul hP hm0) hQ, fun a i hi => ?_, fun i j hj1 hj2 hi => ?_⟩
  · rw [key, Finset.sum_eq_zero, add_zero]
    intro p _
    refine Finset.sum_eq_zero fun l _ => ?_
    have ha := a.isLt
    by_cases hp : p = eI k r a
    · subst hp
      by_cases hl : a.val ≤ l.val
      · rw [Matrix.sub_apply, hm1 a l hl, Matrix.one_apply]; simp
      · have : i ≠ l := by rintro rfl; exact hl hi
        rw [(bP l (Or.inl (by omega)) i).1, if_neg this]; simp
    · rw [(bQ (eI k r a) (Or.inl ha) p).1, if_neg hp]; simp
  · rw [key, Finset.sum_eq_zero, add_zero]
    intro p _
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hp : p.val < r ∨ r + k < p.val
    · have : j ≠ p := by rintro rfl; omega
      rw [(bQ p hp j).2, if_neg this]; simp
    · by_cases hl : r ≤ l.val
      · rw [Matrix.sub_apply, hm2 l p (by omega) (by omega) hl, Matrix.one_apply]; simp
      · have : i ≠ l := by rintro rfl; exact hl hi
        rw [(bP l (Or.inl (by omega)) i).1, if_neg this]; simp

theorem dg_mem {d : Fin (2 * r + k + 1) → ℝ} (hd : IsTor k r d) : dg d ∈ UH (Hq k r) := by
  obtain ⟨-, h2, h3, -⟩ := hd
  show (dg d)ᴴ * Hq k r * dg d = Hq k r
  ext i j
  simp only [dg, diagonal_conjTranspose, mul_diagonal, diagonal_mul, Pi.star_apply, Complex.star_def,
    Complex.conj_ofReal, Hq]
  split_ifs with h h' h'
  · rw [mul_one, ← Complex.ofReal_mul, h2 i j h h', Complex.ofReal_one]
  · simp
  · subst h'; rw [h3 i h]; simp
  · simp

theorem dg_mul (t t' : Fin (2 * r + k + 1) → ℝ) : dg t * dg t' = dg (fun i => t i * t' i) := by
  simp [dg, diagonal_mul_diagonal]

theorem isTor_mul {t t' : Fin (2 * r + k + 1) → ℝ} (h : IsTor k r t) (h' : IsTor k r t') :
    IsTor k r (fun i => t i * t' i) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨g1, g2, g3, g4⟩ := h'
  refine ⟨fun i => mul_pos (h1 i) (g1 i), fun i j hi hij => ?_, fun i hi => ?_, ?_⟩
  · have a := h2 i j hi hij
    have b := g2 i j hi hij
    show t i * t' i * (t j * t' j) = 1
    rw [mul_mul_mul_comm, a, b, one_mul]
  · show t i * t' i = 1
    rw [h3 i hi, g3 i hi, one_mul]
  · exact mul_le_one₀ h4 (g1 _).le g4

theorem dg_comm {t : Fin (2 * r + k + 1) → ℝ} (ht : IsTor k r t) (ht0 : t (wI k r 0) = 1)
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ Wbq k r) : dg t * h = h * dg t := by
  have b := block_of_fix hh.1 (fun a => ⟨hq_e a, hq_es a⟩) (fun a => ⟨hq_e a, hq_es a⟩) hh.2
  obtain ⟨-, h2, h3, -⟩ := ht
  have mid : ∀ i : Fin (2 * r + k + 1), ¬ (i.val < r ∨ r + k < i.val) → t i = 1 := by
    intro i hi
    by_cases ho : outer k r i
    · by_cases h0 : i.val = r
      · have : i = wI k r 0 := Fin.ext (by simp [wI, h0])
        rw [this, ht0]
      · have := h2 i (wI k r 0) ho (by unfold outer at ho; simp only [wI, Fin.val_zero]; omega)
        rwa [ht0, mul_one] at this
    · exact h3 i ho
  ext i j
  simp only [dg, mul_diagonal, diagonal_mul]
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [(b i hi j).2]
    split_ifs with e
    · subst e; simp
    · simp
  · by_cases hj : j.val < r ∨ r + k < j.val
    · rw [(b j hj i).1]
      split_ifs with e
      · subst e; simp
      · simp
    · rw [mid i hi, mid j hj]; simp

theorem decomp : AdaptExists → IwaQ → LeviQ → CartanQ → Decomp := by
  intro hA hI hL hC k r z Γ hk _ hΓ g hg
  obtain ⟨⟨Γ₀, hu0, hΓ0⟩, -⟩ := hA k r hk
  obtain ⟨hΓi, hΓf, ρ, -, hz⟩ := hΓ
  obtain ⟨Γ', hΓ1, hΓ2⟩ := iso_exists_inv hΓi hq_sq
  have hu0' : Γ₀ * Γ₀ᴴ = 1 := mul_eq_one_comm.mp hu0
  have hΓ'i := iso_inv hΓi hΓ1
  have hx : Γ' * g * Γ₀ ∈ UH (Hq k r) := iso_mul (iso_mul hΓ'i hg) hΓ0
  obtain ⟨s, hs, κ₁, hκ₁, hst, hu1, e1⟩ := hI k r hk _ hx
  obtain ⟨m, hm, t, μ, hμ, κ₂, hκ₂, ht, ht0, hu2, e2⟩ := hL k r hk s hs hst
  obtain ⟨h, hh, t', κ₃, hκ₃, hfix, ht', -, hu3, e3⟩ := hC k r hk μ hμ
  obtain ⟨h', hh1, hh2⟩ := iso_exists_inv hh.1 hq_sq
  have hh'i := iso_inv hh.1 hh1
  have hd := isTor_mul ht ht'
  refine ⟨Γ * h * Γ', ⟨iso_mul (iso_mul hΓi hh.1) hΓ'i, fun a => ⟨?_, ?_⟩, ?_⟩, (Γ * h') * m * (h * Γ'), ?_,
    fun i => t i * t' i, κ₃ * κ₂ * κ₁ * Γ₀ᴴ, hd, ?_, ?_, ?_⟩
  · exact fix_mul (fix_mul (hΓf a).1 (hh.2 a).1) (fix_inv hΓ2 (hΓf a).1)
  · exact fix_mul (fix_mul (hΓf a).2 (hh.2 a).2) (fix_inv hΓ2 (hΓf a).2)
  · rw [hz, mulVec_smul, mulVec_mulVec, Matrix.mul_assoc, hΓ2, Matrix.mul_one, ← mulVec_mulVec, hfix]
  · refine conj_mem_N (iso_mul hΓi hh'i) ?_ ?_ (fun a => ⟨?_, ?_⟩) hm
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc h', hh2, Matrix.one_mul, hΓ1]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Γ', hΓ2, Matrix.one_mul, hh1]
    · exact fix_mul (hΓf a).1 (fix_inv hh2 (hh.2 a).1)
    · exact fix_mul (hΓf a).2 (fix_inv hh2 (hh.2 a).2)
  · exact uni_mul (uni_mul (uni_mul hu3 hu2) hu1) (by rw [conjTranspose_conjTranspose]; exact hu0')
  · exact iso_mul (iso_mul hΓi (dg_mem hd)) (iso_mul (iso_mul (iso_mul hκ₃ hκ₂) hκ₁) (iso_inv hΓ0 hu0'))
  · have eg : g = Γ * (Γ' * g * Γ₀) * Γ₀ᴴ := by
      simp only [← Matrix.mul_assoc]
      rw [hΓ1, Matrix.one_mul, Matrix.mul_assoc, hu0', Matrix.mul_one]
    have c1 : ∀ X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Γ' * (Γ * X) = X := fun X => by
      rw [← Matrix.mul_assoc, hΓ2, Matrix.one_mul]
    have c2 : ∀ X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, h * (h' * X) = X := fun X => by
      rw [← Matrix.mul_assoc, hh1, Matrix.one_mul]
    have c3 : ∀ X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, dg t * (h * X) = h * (dg t * X) :=
      fun X => by rw [← Matrix.mul_assoc, dg_comm ht ht0 hh, Matrix.mul_assoc]
    rw [eg, e1, e2, e3, ← dg_mul]
    simp only [Matrix.mul_assoc, c1, c2, c3]

end GlobalTheory.CompanionTheory.BmuDecomp
