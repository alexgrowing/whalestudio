import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

section CayleyAux

variable {n : ℕ}

def szcMk (τ : Fin n → Fin n) (d o : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (if j = i then d i else 0) + (if j = τ i then o i else 0)

theorem szcMk_mul_apply (τ : Fin n → Fin n) (d o : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) : (szcMk τ d o * M) i j = d i * M i j + o i * M (τ i) j := by
  rw [Matrix.mul_apply]
  simp only [szcMk, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem szcMk_mul (τ : Fin n → Fin n) (hτ : ∀ i, τ (τ i) = i) (d o d' o' : Fin n → ℂ) :
    szcMk τ d o * szcMk τ d' o' =
      szcMk τ (fun i => d i * d' i + o i * o' (τ i)) (fun i => d i * o' i + o i * d' (τ i)) := by
  ext i j
  rw [szcMk_mul_apply]
  simp only [szcMk, hτ]
  split_ifs <;> ring

theorem szcMk_conjTranspose (τ : Fin n → Fin n) (hτ : ∀ i, τ (τ i) = i) (d o : Fin n → ℂ) :
    (szcMk τ d o)ᴴ = szcMk τ (fun i => star (d i)) (fun i => star (o (τ i))) := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  simp only [szcMk]
  have key : (i = τ j) ↔ (j = τ i) := ⟨fun h => by rw [h, hτ], fun h => by rw [h, hτ]⟩
  by_cases h1 : j = i
  · subst h1
    by_cases h : j = τ j
    · simp [← h]
    · simp [h]
  · by_cases h2 : j = τ i
    · subst h2
      simp [hτ, h1, Ne.symm h1]
    · have h3 : ¬ i = τ j := fun h => h2 (key.mp h)
      simp [h1, Ne.symm h1, h2, h3]

theorem szcMk_zero (τ : Fin n → Fin n) (d : Fin n → ℂ) : szcMk τ d 0 = Matrix.diagonal d := by
  ext i j
  simp only [szcMk, Matrix.diagonal_apply, Pi.zero_apply, ite_self, add_zero]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

end CayleyAux

section Cayley48

def szcTau (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if i.val < r ∨ r + k < i.val then ⟨2 * r + k - i.val, by omega⟩ else i

theorem szcTau_val (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    (szcTau k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := by
  unfold szcTau; split_ifs <;> rfl

theorem szc_tau_pos {k r : ℕ} {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) :
    (szcTau k r i).val = 2 * r + k - i.val := by
  rw [szcTau_val, if_pos h]

theorem szc_tau_neg {k r : ℕ} {i : Fin (2 * r + k + 1)} (h : ¬ (i.val < r ∨ r + k < i.val)) :
    szcTau k r i = i := by
  unfold szcTau; rw [if_neg h]

theorem szcTau_tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : szcTau k r (szcTau k r i) = i := by
  have := i.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · apply Fin.ext
    have h' : (szcTau k r i).val < r ∨ r + k < (szcTau k r i).val := by rw [szc_tau_pos h]; omega
    rw [szc_tau_pos h', szc_tau_pos h]
    omega
  · rw [szc_tau_neg h, szc_tau_neg h]

def szcS : ℂ := ((Real.sqrt 2 / 2 : ℝ) : ℂ)

theorem szcS_sq : szcS * szcS = 1 / 2 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2 : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = (1 / 2 : ℝ) := by nlinarith [h]
  unfold szcS
  rw [← Complex.ofReal_mul, h2]
  push_cast
  ring

theorem szcS_star : star szcS = szcS := by
  unfold szcS
  rw [Complex.star_def]
  exact Complex.conj_ofReal _

def szcC (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then szcS else if r + k < i.val then -szcS else 1

def szcO (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r ∨ r + k < i.val then szcS else 0

def szcHD (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r ∨ r + k < i.val then 0 else if i.val = r + k then -1 else 1

def szcHO (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r ∨ r + k < i.val then 1 else 0

def szcD (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r + k then 1 else -1

theorem szcO_tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : szcO k r (szcTau k r i) = szcO k r i := by
  have := i.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · unfold szcO; rw [szc_tau_pos h]; split_ifs <;> first | rfl | omega
  · rw [szc_tau_neg h]

theorem szcHO_tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : szcHO k r (szcTau k r i) = szcHO k r i := by
  have := i.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · unfold szcHO; rw [szc_tau_pos h]; split_ifs <;> first | rfl | omega
  · rw [szc_tau_neg h]

theorem szcHD_tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : szcHD k r (szcTau k r i) = szcHD k r i := by
  have := i.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · unfold szcHD; rw [szc_tau_pos h]; split_ifs <;> first | rfl | omega
  · rw [szc_tau_neg h]

theorem szcC_tau (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    szcC k r (szcTau k r i) = if i.val < r then -szcS else if r + k < i.val then szcS else 1 := by
  have := i.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · unfold szcC; rw [szc_tau_pos h]; split_ifs <;> first | rfl | omega
  · rw [szc_tau_neg h]; unfold szcC; split_ifs <;> first | rfl | omega

theorem szc_Hpk (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r = szcMk (szcTau k r) (szcHD k r) (szcHO k r) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · have ht := szc_tau_pos h
    simp only [Formalism.QuantumDeterminants.Hpk, szcMk, szcHD, szcHO, Fin.ext_iff, ht]
    split_ifs <;> first | omega | norm_num
  · have ht := szc_tau_neg h
    simp only [Formalism.QuantumDeterminants.Hpk, szcMk, szcHD, szcHO, ht, Fin.ext_iff]
    split_ifs <;> first | omega | norm_num

theorem szc_CC (k r : ℕ) :
    szcMk (szcTau k r) (szcC k r) (szcO k r) * szcMk (szcTau k r) (szcC k r) (szcO k r) = 1 := by
  rw [szcMk_mul _ (szcTau_tau k r), ← Matrix.diagonal_one, ← szcMk_zero (szcTau k r)]
  congr 1
  · funext i
    have := i.isLt
    simp only [szcO_tau]
    unfold szcC szcO
    split_ifs <;> first | omega | ring1 | linear_combination 2 * szcS_sq
  · funext i
    have := i.isLt
    simp only [szcC_tau, Pi.zero_apply]
    unfold szcC szcO
    split_ifs <;> first | omega | ring1

theorem szc_Cstar (k r : ℕ) :
    (szcMk (szcTau k r) (szcC k r) (szcO k r))ᴴ = szcMk (szcTau k r) (szcC k r) (szcO k r) := by
  rw [szcMk_conjTranspose _ (szcTau_tau k r)]
  congr 1
  · funext i; unfold szcC; split_ifs <;> simp [szcS_star]
  · funext i; simp only [szcO_tau]; unfold szcO; split_ifs <;> simp [szcS_star]

theorem szc_CHC (k r : ℕ) :
    szcMk (szcTau k r) (szcC k r) (szcO k r) * Formalism.QuantumDeterminants.Hpk k r *
      szcMk (szcTau k r) (szcC k r) (szcO k r) = Matrix.diagonal (szcD k r) := by
  rw [szc_Hpk, szcMk_mul _ (szcTau_tau k r), szcMk_mul _ (szcTau_tau k r), ← szcMk_zero (szcTau k r)]
  congr 1
  · funext i
    have := i.isLt
    simp only [szcO_tau, szcHO_tau, szcHD_tau]
    unfold szcC szcO szcHD szcHO szcD
    split_ifs <;> first | omega | ring1 | linear_combination 2 * szcS_sq |
      linear_combination (-2) * szcS_sq
  · funext i
    have := i.isLt
    simp only [szcHO_tau, szcHD_tau, szcC_tau, Pi.zero_apply]
    unfold szcC szcO szcHD szcHO
    split_ifs <;> first | omega | ring1

def szcEqvF (k r : ℕ) (hk : 1 ≤ k) :
    {i : Fin (2 * r + k + 1) // Formalism.MainNotions.CayleySignature.eps48 k r i = false} ≃ Fin (r + 1) where
  toFun i := ⟨(i.1.val - k) / 2, by have := i.1.isLt; omega⟩
  invFun b := ⟨⟨k + 2 * b.val, by have := b.isLt; omega⟩, by
    have hb : ¬ (k + 2 * b.val < k - 1) := by omega
    have hb2 : ¬ ((k + 2 * b.val - (k - 1)) % 2 = 0) := by omega
    simp [Formalism.MainNotions.CayleySignature.eps48, hb, hb2]⟩
  left_inv i := by
    obtain ⟨i, hi⟩ := i
    have hlt := i.isLt
    have h1 : ¬ (i.val < k - 1) := by
      intro h1; simp [Formalism.MainNotions.CayleySignature.eps48, h1] at hi
    have h2 : ¬ ((i.val - (k - 1)) % 2 = 0) := by
      intro h2; simp [Formalism.MainNotions.CayleySignature.eps48, h1, h2] at hi
    apply Subtype.ext
    apply Fin.ext
    show k + 2 * ((i.val - k) / 2) = i.val
    omega
  right_inv b := by
    apply Fin.ext
    show (k + 2 * b.val - k) / 2 = b.val
    omega

def szcEqvT (k r : ℕ) : {j : Fin (2 * r + k + 1) // r + k ≤ j.val} ≃ Fin (r + 1) where
  toFun j := ⟨j.1.val - (r + k), by have := j.1.isLt; omega⟩
  invFun b := ⟨⟨r + k + b.val, by have := b.isLt; omega⟩, by show r + k ≤ r + k + b.val; omega⟩
  left_inv j := by
    obtain ⟨j, hj⟩ := j
    apply Subtype.ext
    apply Fin.ext
    show r + k + (j.val - (r + k)) = j.val
    omega
  right_inv b := by
    apply Fin.ext
    show r + k + b.val - (r + k) = b.val
    omega

theorem szc_exists_perm (k r : ℕ) (hk : 1 ≤ k) :
    ∃ π : Fin (2 * r + k + 1) ≃ Fin (2 * r + k + 1),
      ∀ i, (Formalism.MainNotions.CayleySignature.eps48 k r i = false ↔ r + k ≤ (π i).val) := by
  classical
  let e : {i : Fin (2 * r + k + 1) // Formalism.MainNotions.CayleySignature.eps48 k r i = false} ≃
      {j : Fin (2 * r + k + 1) // r + k ≤ j.val} := (szcEqvF k r hk).trans (szcEqvT k r).symm
  have hc : Fintype.card {i : Fin (2 * r + k + 1) // ¬ Formalism.MainNotions.CayleySignature.eps48 k r i = false} =
      Fintype.card {j : Fin (2 * r + k + 1) // ¬ r + k ≤ j.val} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, Fintype.card_congr e]
  obtain ⟨f⟩ := Fintype.card_eq.mp hc
  refine ⟨Equiv.subtypeCongr e f, fun i => ?_⟩
  by_cases h : Formalism.MainNotions.CayleySignature.eps48 k r i = false
  · have hx : Equiv.subtypeCongr e f i = (e ⟨i, h⟩ : Fin (2 * r + k + 1)) := by
      simp [Equiv.subtypeCongr, h]
    rw [hx]
    exact ⟨fun _ => (e ⟨i, h⟩).2, fun _ => h⟩
  · have hx : Equiv.subtypeCongr e f i = (f ⟨i, h⟩ : Fin (2 * r + k + 1)) := by
      simp [Equiv.subtypeCongr, h]
    rw [hx]
    exact ⟨fun h' => absurd h' h, fun h' => absurd h' (f ⟨i, h⟩).2⟩

end Cayley48

end ReciprocityTheory.ChartRestriction.DS
