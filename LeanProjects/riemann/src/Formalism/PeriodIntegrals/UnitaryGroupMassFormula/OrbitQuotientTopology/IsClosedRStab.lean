import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.FlagMatLower

open Matrix

noncomputable section

namespace PI.AmpOrbQuot

open Formalism.QuantumDeterminants Formalism.MainNotions.S PI.AmpRootCommon

variable {k r : ℕ}

def nβ (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℕ :=
  if i.val < r then i.val else if i.val ≤ r + k then r else r + 1

theorem nβ_X {i : Fin (2 * r + k + 1)} (h : i.val < r) : nβ k r i = i.val := by
  unfold nβ
  rw [if_pos h]

theorem nβ_S {i : Fin (2 * r + k + 1)} (h : r + k < i.val) : nβ k r i = r + 1 := by
  unfold nβ
  split_ifs <;> omega

def NDiag (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ i j, nβ k r i = nβ k r j → nβ k r j ≤ r → a i j = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j

theorem nset_iff (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    a ∈ Nset k r ↔ a ∈ UH (Hpk k r) ∧ a.BlockTriangular (nβ k r) ∧ NDiag a := by
  have hE : ∀ (j : Fin (2 * r + k + 1)) (hj : j.val < r), eI k r ⟨j.val, hj⟩ = j :=
    fun j hj => Fin.ext rfl
  constructor
  · rintro ⟨hU, h2, h3⟩
    refine ⟨hU, ?_, ?_⟩
    · intro i j hij
      have hne : i ≠ j := by
        rintro rfl
        exact lt_irrefl _ hij
      unfold nβ at hij
      by_cases hj : j.val < r
      · have hle : j.val ≤ i.val := by split_ifs at hij <;> omega
        have := h2 ⟨j.val, hj⟩ i hle
        rw [hE j hj, if_neg hne] at this
        exact this
      · have hj2 : j.val ≤ r + k := by split_ifs at hij <;> omega
        have hi : r ≤ i.val := by split_ifs at hij <;> omega
        have := h3 i j (by omega) hj2 hi
        rw [if_neg hne] at this
        exact this
    · intro i j hij hjr
      unfold nβ at hij hjr
      rw [Matrix.one_apply]
      by_cases hj : j.val < r
      · have hv : i.val = j.val := by split_ifs at hij <;> omega
        have hieq : i = j := Fin.ext hv
        have := h2 ⟨j.val, hj⟩ i (by show j.val ≤ i.val; omega)
        rw [hE j hj] at this
        exact this
      · have hj2 : j.val ≤ r + k := by split_ifs at hjr <;> omega
        have hi : r ≤ i.val := by split_ifs at hij <;> omega
        exact h3 i j (by omega) hj2 hi
  · rintro ⟨hU, hB, hD⟩
    refine ⟨hU, ?_, ?_⟩
    · intro b i hbi
      have hjv : (eI k r b).val = b.val := rfl
      have hb := b.isLt
      by_cases hie : i = eI k r b
      · rw [if_pos hie, hie]
        have := hD (eI k r b) (eI k r b) rfl (by unfold nβ; split_ifs <;> omega)
        rw [this, Matrix.one_apply_eq]
      · rw [if_neg hie]
        have hne : i.val ≠ b.val := fun h => hie (Fin.ext (by rw [h, hjv]))
        apply hB
        unfold nβ
        split_ifs <;> omega
    · intro i j hj1 hj2 hi
      by_cases hij : i = j
      · rw [if_pos hij, hij]
        have := hD j j rfl (by unfold nβ; split_ifs <;> omega)
        rw [this, Matrix.one_apply_eq]
      · rw [if_neg hij]
        have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
        by_cases hik : i.val ≤ r + k
        · have := hD i j (by unfold nβ; split_ifs <;> omega) (by unfold nβ; split_ifs <;> omega)
          rw [this, Matrix.one_apply_ne hij]
        · apply hB
          unfold nβ
          split_ifs <;> omega

theorem uh_mul {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ UH (Hpk k r))
    (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

theorem uh_inv {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ UH (Hpk k r)) :
    a⁻¹ ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
  calc (a⁻¹)ᴴ * Hpk k r * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) * a⁻¹ := by rw [ha']
    _ = (a * a⁻¹)ᴴ * Hpk k r * (a * a⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [uh_mul_inv ha, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem ndiag_term {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hA : a.BlockTriangular (nβ k r)) (hB : b.BlockTriangular (nβ k r)) (hDa : NDiag a)
    (i j l : Fin (2 * r + k + 1)) (hij : nβ k r i = nβ k r j) (hjr : nβ k r j ≤ r) :
    a i l * b l j = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i l * b l j := by
  rcases lt_trichotomy (nβ k r l) (nβ k r i) with h | h | h
  · rw [hA h]
    by_cases hil : i = l
    · subst hil
      exact absurd h (lt_irrefl _)
    · rw [Matrix.one_apply_ne hil]
  · rw [hDa i l h.symm (by rw [h, hij]; exact hjr)]
  · rw [hB (show nβ k r j < nβ k r l by rw [← hij]; exact h)]
    simp

theorem ndiag_mul {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hA : a.BlockTriangular (nβ k r)) (hB : b.BlockTriangular (nβ k r)) (hDa : NDiag a) (hDb : NDiag b) :
    NDiag (a * b) := by
  intro i j hij hjr
  rw [Matrix.mul_apply, Finset.sum_congr rfl (fun l _ => ndiag_term hA hB hDa i j l hij hjr),
    ← Matrix.mul_apply, Matrix.one_mul]
  exact hDb i j hij hjr

theorem ndiag_inv {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hU : a ∈ UH (Hpk k r)) (hA : a.BlockTriangular (nβ k r)) (hDa : NDiag a) : NDiag a⁻¹ := by
  have h1 : a * a⁻¹ = 1 := uh_mul_inv hU
  letI : Invertible a := ⟨a⁻¹, uh_inv_mul hU, h1⟩
  have hB : a⁻¹.BlockTriangular (nβ k r) := Matrix.blockTriangular_inv_of_blockTriangular hA
  intro i j hij hjr
  have := congrFun (congrFun h1 i) j
  rw [Matrix.mul_apply, Finset.sum_congr rfl (fun l _ => ndiag_term hA hB hDa i j l hij hjr),
    ← Matrix.mul_apply, Matrix.one_mul] at this
  exact this

theorem nset_one : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Nset k r := by
  rw [nset_iff]
  refine ⟨?_, Matrix.blockTriangular_one, fun i j _ _ => rfl⟩
  show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem nset_mul {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ Nset k r)
    (hb : b ∈ Nset k r) : a * b ∈ Nset k r := by
  rw [nset_iff] at ha hb ⊢
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  exact ⟨uh_mul ha1 hb1, ha2.mul hb2, ndiag_mul ha2 hb2 ha3 hb3⟩

theorem nset_inv {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ Nset k r) :
    a⁻¹ ∈ Nset k r := by
  rw [nset_iff] at ha ⊢
  obtain ⟨h1, h2, h3⟩ := ha
  have hh : a * a⁻¹ = 1 := uh_mul_inv h1
  letI : Invertible a := ⟨a⁻¹, uh_inv_mul h1, hh⟩
  exact ⟨uh_inv h1, Matrix.blockTriangular_inv_of_blockTriangular h2, ndiag_inv h1 h2 h3⟩

theorem nset_uh {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ Nset k r) :
    a ∈ UH (Hpk k r) := ha.1

section R

variable {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem conj_mul (hg : g ∈ UH (Hpk k r)) (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by
  have h : g * g⁻¹ = 1 := uh_mul_inv hg
  calc g⁻¹ * (a * b) * g = g⁻¹ * a * (g * g⁻¹) * b * g := by
        rw [h, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by simp only [Matrix.mul_assoc]

theorem conj_inv (hg : g ∈ UH (Hpk k r)) {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) : (g⁻¹ * a * g)⁻¹ = g⁻¹ * a⁻¹ * g := by
  apply Matrix.inv_eq_right_inv
  have h1 : g * g⁻¹ = 1 := uh_mul_inv hg
  have h2 : g⁻¹ * g = 1 := uh_inv_mul hg
  have h3 : a * a⁻¹ = 1 := uh_mul_inv ha
  calc g⁻¹ * a * g * (g⁻¹ * a⁻¹ * g) = g⁻¹ * (a * (g * g⁻¹) * a⁻¹) * g := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_one, h3, Matrix.mul_one, h2]

theorem rstab_one (hg : g ∈ UH (Hpk k r)) :
    (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ RStab k r g := ⟨nset_one, by rw [Matrix.mul_one, uh_inv_mul hg]; exact nset_one⟩

theorem rstab_mul (hg : g ∈ UH (Hpk k r)) {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ RStab k r g) (hb : b ∈ RStab k r g) : a * b ∈ RStab k r g := ⟨nset_mul ha.1 hb.1, by rw [conj_mul hg]; exact nset_mul ha.2 hb.2⟩

theorem rstab_inv (hg : g ∈ UH (Hpk k r)) {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ RStab k r g) : a⁻¹ ∈ RStab k r g := ⟨nset_inv ha.1, by rw [← conj_inv hg (nset_uh ha.1)]; exact nset_inv ha.2⟩

end R

theorem isClosed_UH : IsClosed (UH (Hpk k r)) := isClosed_eq (((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const

theorem isClosed_Nset : IsClosed (Nset k r) := by
  have hE : ∀ (i j : Fin (2 * r + k + 1)) (c : ℂ),
      IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | g i j = c} :=
    fun i j c => isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const
  show IsClosed {g | g ∈ UH (Hpk k r) ∧
    (∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      g i (eI k r a) = if i = eI k r a then 1 else 0) ∧
    (∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
      g i j = if i = j then 1 else 0)}
  rw [Set.setOf_and, Set.setOf_and, Set.setOf_mem_eq]
  refine isClosed_UH.inter (IsClosed.inter ?_ ?_)
  · simp only [Set.setOf_forall]
    exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ => hE _ _ _
  · simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => hE _ _ _

theorem isClosed_RStab (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : IsClosed (RStab k r g) := by
  show IsClosed {a | a ∈ Nset k r ∧ g⁻¹ * a * g ∈ Nset k r}
  rw [Set.setOf_and, Set.setOf_mem_eq]
  exact isClosed_Nset.inter (IsClosed.preimage (f := fun a => g⁻¹ * a * g)
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const) isClosed_Nset)

end PI.AmpOrbQuot
