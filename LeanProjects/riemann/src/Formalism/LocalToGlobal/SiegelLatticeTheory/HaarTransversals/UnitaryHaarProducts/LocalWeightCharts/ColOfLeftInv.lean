import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HCReprodM

open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S

noncomputable section

namespace WlocSk.UnitaryGroupBasics

variable {k r : ℕ}

def col (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ i j : Fin (2 * r + k + 1), j.val ≤ r + k → (j.val ≤ i.val ∨ r ≤ i.val) →
    g i j = if i = j then 1 else 0

def block (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  (∀ i j : Fin (2 * r + k + 1), (j.val < r ∨ r + k < j.val) → g i j = if i = j then 1 else 0) ∧
  (∀ i j : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → g i j = if i = j then 1 else 0)

theorem nset_iff (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    g ∈ Nset k r ↔ g ∈ UH (Hpk k r) ∧ col k r g := by
  constructor
  · rintro ⟨hU, h2, h3⟩
    refine ⟨hU, fun i j hj hi => ?_⟩
    by_cases hjr : j.val < r
    · have e : eI k r ⟨j.val, hjr⟩ = j := Fin.ext rfl
      have := h2 ⟨j.val, hjr⟩ i (by simp only [eI] at *; omega)
      rw [e] at this
      exact this
    · exact h3 i j (by omega) hj (by omega)
  · rintro ⟨hU, hc⟩
    refine ⟨hU, fun a i hi => ?_, fun i j h1 h2 h3 => ?_⟩
    · exact hc i (eI k r a) (by simp only [eI]; omega) (by simp only [eI]; omega)
    · exact hc i j h2 (by omega)

theorem col_mul {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : col k r g) (hh : col k r h) : col k r (g * h) := by
  intro i j hj hi
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [hh j j hj (by omega), if_pos rfl, mul_one]
    exact hg i j hj hi
  · intro m _ hmj
    by_cases hm : j.val ≤ m.val ∨ r ≤ m.val
    · rw [hh m j hj hm, if_neg hmj, mul_zero]
    · push Not at hm
      have hne : i ≠ m := by
        intro e
        subst e
        omega
      rw [hg i m (by omega) (by omega), if_neg hne, zero_mul]
  · intro hj'
    exact absurd (Finset.mem_univ j) hj'

theorem col_of_left_inv {g g' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : col k r g) (hm : g' * g = 1) : col k r g' := by
  have key : ∀ n : ℕ, ∀ i j : Fin (2 * r + k + 1), j.val < n → j.val ≤ r + k →
      (j.val ≤ i.val ∨ r ≤ i.val) → g' i j = if i = j then 1 else 0 := by
    intro n
    induction n with
    | zero => intro i j h; omega
    | succ n ih =>
      intro i j hjn hj hi
      have e := congrFun (congrFun hm i) j
      rw [Matrix.mul_apply, Finset.sum_eq_single j] at e
      · rw [hg j j hj (by omega), if_pos rfl, mul_one] at e
        rw [e, Matrix.one_apply]
      · intro m _ hmj
        by_cases hmc : j.val ≤ m.val ∨ r ≤ m.val
        · rw [hg m j hj hmc, if_neg hmj, mul_zero]
        · push Not at hmc
          have hne : i ≠ m := by
            intro e
            subst e
            omega
          rw [ih i m (by omega) (by omega) (by omega), if_neg hne, zero_mul]
      · intro hj'
        exact absurd (Finset.mem_univ j) hj'
  intro i j hj hi
  exact key (j.val + 1) i j (by omega) hj hi

def tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩

def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

theorem hpk_row (i m : Fin (2 * r + k + 1)) :
    Hpk k r i m = if m = tau k r i then sgn k r i else 0 := by
  unfold Hpk tau sgn
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mul_apply (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) : (Hpk k r * A) i j = sgn k r i * A (tau k r i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (tau k r i)]
  · rw [hpk_row, if_pos rfl]
  · intro m _ hm
    rw [hpk_row, if_neg hm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem tau_tau (i : Fin (2 * r + k + 1)) : tau k r (tau k r i) = i := by
  unfold tau
  apply Fin.ext
  simp only
  split_ifs <;> omega

theorem sgn_tau (i : Fin (2 * r + k + 1)) : sgn k r (tau k r i) = sgn k r i := by
  unfold sgn tau
  simp only
  split_ifs <;> first | rfl | (exfalso; omega)

theorem sgn_mul_self (i : Fin (2 * r + k + 1)) : sgn k r i * sgn k r i = 1 := by
  unfold sgn
  split_ifs <;> norm_num

theorem hpk_sq : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [hpk_mul_apply, hpk_row, tau_tau, sgn_tau, Matrix.one_apply]
  by_cases h : j = i
  · rw [if_pos h, if_pos h.symm, sgn_mul_self]
  · rw [if_neg h, if_neg (Ne.symm h), mul_zero]

theorem isUnit_of_uh {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : IsUnit g.det := by
  apply Matrix.isUnit_det_of_left_inverse (B := Hpk k r * gᴴ * Hpk k r)
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hpk_sq]

theorem uh_mul {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) (hh : h ∈ UH (Hpk k r)) : g * h ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  rw [conjTranspose_mul]
  calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']

theorem uh_inv {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : g⁻¹ ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hu := isUnit_of_uh hg
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by
        rw [Matrix.mul_nonsing_inv _ hu, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem mem_n_mul {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Nset k r) (hh : h ∈ Nset k r) : g * h ∈ Nset k r := by
  rw [nset_iff] at *
  exact ⟨uh_mul hg.1 hh.1, col_mul hg.2 hh.2⟩

theorem mem_n_inv {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Nset k r) : g⁻¹ ∈ Nset k r := by
  rw [nset_iff] at *
  exact ⟨uh_inv hg.1, col_of_left_inv hg.2 (Matrix.nonsing_inv_mul _ (isUnit_of_uh hg.1))⟩

theorem mul_apply_add {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : col k r g) (hh : col k r h) (i j : Fin (2 * r + k + 1)) (hir : i.val < r)
    (hj : j.val ≤ r + k) (hij : i.val < j.val) (hji : j.val ≤ i.val + 1 ∨ r ≤ i.val + 1) :
    (g * h) i j = g i j + h i j := by
  have term : ∀ m : Fin (2 * r + k + 1),
      g i m * h m j = (if m = i then h i j else 0) + (if m = j then g i j else 0) := by
    intro m
    by_cases hmi : m.val ≤ i.val
    · rw [hg i m (by omega) (Or.inl hmi)]
      have hmj : m ≠ j := by
        intro e
        subst e
        omega
      rw [if_neg hmj, add_zero]
      by_cases e : m = i
      · subst e
        rw [if_pos rfl, if_pos rfl, one_mul]
      · rw [if_neg (Ne.symm e), if_neg e, zero_mul]
    · rw [hh m j hj (by omega)]
      have hm : m ≠ i := by
        intro e
        subst e
        omega
      rw [if_neg hm, zero_add]
      by_cases e : m = j
      · subst e
        rw [if_pos rfl, if_pos rfl, mul_one]
      · rw [if_neg e, if_neg e, mul_zero]
  rw [Matrix.mul_apply, Finset.sum_congr rfl (fun m _ => term m), Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _),
    add_comm]

theorem ellA_mul (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : col k r g) (hh : col k r h) (a : Fin r) : ellA k r z (g * h) a = ellA k r z g a + ellA k r z h a := by
  unfold ellA
  by_cases ha : a.val + 1 < r
  · rw [dif_pos ha, dif_pos ha, dif_pos ha]
    exact mul_apply_add hg hh _ _ (by simp only [eI]; omega) (by simp only [eI]; omega)
      (by simp only [eI]; omega) (by simp only [eI]; omega)
  · rw [dif_neg ha, dif_neg ha, dif_neg ha]
    simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hzj : z j = 0
    · rw [hzj, mul_zero, mul_zero, mul_zero, add_zero]
    · have hjW : r ≤ j.val ∧ j.val ≤ r + k := by
        by_contra hc
        apply hzj
        apply hz
        omega
      rw [mul_apply_add hg hh _ _ (by simp only [eI]; omega) (by omega)
        (by simp only [eI]; omega) (by simp only [eI]; omega), add_mul]

theorem psiGen_mul (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (hz : inWb k r z)
    {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Nset k r) (hh : h ∈ Nset k r) :
    psiGen k r z c (g * h) = psiGen k r z c g * psiGen k r z c h := by
  have hs : (∑ a, c a * ellA k r z (g * h) a) = (∑ a, c a * ellA k r z g a) + ∑ a, c a * ellA k r z h a := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [ellA_mul z hz ((nset_iff g).1 hg).2 ((nset_iff h).1 hh).2 a, mul_add]
  unfold psiGen
  rw [hs, Complex.add_re, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem psiGen_norm (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : ‖psiGen k r z c g‖ = 1 := by
  unfold psiGen
  rw [mul_comm Complex.I]
  exact Complex.norm_exp_ofReal_mul_I _

end WlocSk.UnitaryGroupBasics
