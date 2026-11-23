import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertCorner

variable {L : Type} [Field L] {N : ℕ}

def st (σ : L →+* L) (A : Matrix (Fin N) (Fin N) L) : Matrix (Fin N) (Fin N) L := fun i j => σ (A j.rev i.rev)

def dv (σ : L →+* L) (x : Fin N → L) : Fin N → L := fun j => σ (x j.rev)

def H (σ : L →+* L) (x : Fin N → L) (A : Matrix (Fin N) (Fin N) L) (y : Fin N → L) : L := x ⬝ᵥ (A *ᵥ dv σ y)

theorem st_mul (σ : L →+* L) (A B : Matrix (Fin N) (Fin N) L) : st σ (A * B) = st σ B * st σ A := by
  ext i j
  simp only [st, Matrix.mul_apply, map_sum, map_mul]
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun k => by simp only [Fin.revPerm_apply, Fin.rev_rev]; ring)

theorem st_add (σ : L →+* L) (A B : Matrix (Fin N) (Fin N) L) : st σ (A + B) = st σ A + st σ B := by
  ext i j
  simp [st, map_add]

theorem st_one (σ : L →+* L) : st σ (1 : Matrix (Fin N) (Fin N) L) = 1 := by
  ext i j
  rcases eq_or_ne i j with rfl | h
  · simp [st, Matrix.one_apply]
  · simp [st, Matrix.one_apply, h, Ne.symm h, Fin.rev_inj]

theorem dv_vecMul (σ : L →+* L) (x : Fin N → L) (A : Matrix (Fin N) (Fin N) L) :
    dv σ (x ᵥ* A) = st σ A *ᵥ dv σ x := by
  ext j
  simp only [dv, st, Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, map_mul]
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun k => by simp only [Fin.revPerm_apply, Fin.rev_rev]; ring)

theorem H_vecMul (σ : L →+* L) (x y : Fin N → L) (A P Q : Matrix (Fin N) (Fin N) L) :
    H σ (x ᵥ* P) A (y ᵥ* Q) = H σ x (P * A * st σ Q) y := by
  unfold H
  rw [dv_vecMul, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem H_add (σ : L →+* L) (x y : Fin N → L) (A B : Matrix (Fin N) (Fin N) L) :
    H σ x (A + B) y = H σ x A y + H σ x B y := by
  simp only [H, Matrix.add_mulVec, dotProduct_add]

theorem H_neg (σ : L →+* L) (x y : Fin N → L) (A : Matrix (Fin N) (Fin N) L) :
    H σ x (-A) y = -H σ x A y := by
  simp only [H, Matrix.neg_mulVec, dotProduct_neg]

theorem H_smul (σ : L →+* L) (x : Fin N → L) (A : Matrix (Fin N) (Fin N) L) {t : L} (ht : σ t = t) :
    H σ (t • x) A (t • x) = t * t * H σ x A x := by
  have hd : dv σ (t • x) = t • dv σ x := by
    ext j
    simp [dv, ht]
  simp only [H, hd, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

theorem H_conj (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (x y : Fin N → L) (A : Matrix (Fin N) (Fin N) L) :
    σ (H σ x A y) = H σ y (st σ A) x := by
  simp only [H, dv, st, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun k => ?_)
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun i => by simp only [Fin.revPerm_apply, Fin.rev_rev]; ring)

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem isInt_st {σ : L →+* L} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {A : Matrix (Fin N) (Fin N) L} (hA : IsInt A) :
    IsInt (st σ A) := by
  intro i j
  have h := hA j.rev i.rev
  simp only [Formalism.UG.intL, Valuation.mem_integer_iff] at h ⊢
  simp only [st]
  rw [hv]
  exact h

theorem H_mem {σ : L →+* L} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {A : Matrix (Fin N) (Fin N) L} (hA : IsInt A)
    {x : Fin N → L} (hx : ∀ j, x j ∈ intL L) : H σ x A x ∈ intL L := by
  have hs : ∀ a, a ∈ intL L → σ a ∈ intL L := by
    intro a ha
    simp only [Formalism.UG.intL, Valuation.mem_integer_iff] at ha ⊢
    rw [hv]
    exact ha
  simp only [H, dotProduct, Matrix.mulVec, dv]
  exact Subring.sum_mem _ (fun i _ => Subring.mul_mem _ (hx i)
    (Subring.sum_mem _ (fun k _ => Subring.mul_mem _ (hA i k) (hs _ (hx _)))))

private theorem antiJ_mul_apply_eq_apply_rev_fst (M : Matrix (Fin N) (Fin N) L) (i j : Fin N) :
    (antiJ L N * M) i j = M i.rev j := by
  have hi := i.isLt
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
  · simp only [antiJ, Fin.val_rev]
    rw [if_pos (by omega), one_mul]
  · intro k _ hk
    simp only [antiJ]
    rw [if_neg, zero_mul]
    intro h
    apply hk
    ext
    simp only [Fin.val_rev]
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem mul_antiJ_apply_eq_rev_col (M : Matrix (Fin N) (Fin N) L) (i j : Fin N) :
    (M * antiJ L N) i j = M i j.rev := by
  have hj := j.isLt
  rw [Matrix.mul_apply, Finset.sum_eq_single j.rev]
  · simp only [antiJ, Fin.val_rev]
    rw [if_pos (by omega), mul_one]
  · intro k _ hk
    simp only [antiJ]
    rw [if_neg, mul_zero]
    intro h
    apply hk
    ext
    simp only [Fin.val_rev]
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem antiJ_mul_self_eq_one : antiJ L N * antiJ L N = 1 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [antiJ_mul_apply_eq_apply_rev_fst, Matrix.one_apply]
  simp only [antiJ, Fin.val_rev]
  by_cases h : i = j
  · subst h
    rw [if_pos (by omega), if_pos rfl]
  · rw [if_neg (by intro h'; apply h; ext; omega), if_neg h]

private theorem st_eq_antiJ_mul_cT_mul_antiJ (σ : L →+* L) (A : Matrix (Fin N) (Fin N) L) :
    st σ A = antiJ L N * cT σ A * antiJ L N := by
  ext i j
  rw [mul_antiJ_apply_eq_rev_col, antiJ_mul_apply_eq_apply_rev_fst]
  simp [st, cT]

private theorem mat_mul_st_mat_eq_one {σ : L →+* L} (g : GU σ N) : mat g * st σ (mat g) = 1 := by
  have hg : cT σ (mat g) * antiJ L N * mat g = antiJ L N := g.2
  have hst : st σ (mat g) * mat g = 1 := by
    rw [st_eq_antiJ_mul_cT_mul_antiJ, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ (mat g)), hg, antiJ_mul_self_eq_one]
  exact mul_eq_one_comm.mp hst

theorem defect_eq {σ : L →+* L} (g₀ : GU σ N) {U V C : Matrix (Fin N) (Fin N) L}
    (hC : (U + V * mat g₀) * C = 1) :
    -((U + V * mat g₀) * 1 * st σ (U + V * mat g₀)) + (U + V * mat g₀) * (C * V * mat g₀) * st σ (U + V * mat g₀)
      + (U + V * mat g₀) * st σ (C * V * mat g₀) * st σ (U + V * mat g₀)
      = -(U * st σ U) + V * st σ V := by
  have hg : mat g₀ * st σ (mat g₀) = 1 := mat_mul_st_mat_eq_one g₀
  have hCs : st σ C * st σ (U + V * mat g₀) = 1 := by rw [← st_mul, hC, st_one]
  have e1 : (U + V * mat g₀) * (C * V * mat g₀) = V * mat g₀ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hC, Matrix.one_mul]
  have e2 : (U + V * mat g₀) * st σ (C * V * mat g₀) * st σ (U + V * mat g₀)
      = (U + V * mat g₀) * st σ (mat g₀) * st σ V := by
    rw [st_mul, st_mul]
    simp only [Matrix.mul_assoc, hCs, Matrix.mul_one]
  have e3 : V * mat g₀ * st σ (mat g₀) * st σ V = V * st σ V := by
    rw [Matrix.mul_assoc V, hg, Matrix.mul_one]
  rw [Matrix.mul_one, e1, e2, st_add, st_mul]
  calc _ = -(U * st σ U) + V * mat g₀ * st σ (mat g₀) * st σ V := by noncomm_ring
    _ = _ := by rw [e3]

theorem smallCorner_of_heis : Heis → Dual → SmallCorner := by
  intro hH _hDl L _ _ ϖ σ q N hU g₀ U V C hF e f r hef hr
  obtain ⟨h1, -, h3⟩ := hH L ϖ σ q N hU
  obtain ⟨τ, hτ, hτ1⟩ := GlobalTheory.InertZeta.exists_trace_one hU
  obtain ⟨hσ, hv, hϖ, hϖv, -, -, -⟩ := hU
  obtain ⟨hUi, hVi, -, -, hWC⟩ := hF
  have hCW : C * (U + V * mat g₀) = 1 := mul_eq_one_comm.mp hWC
  have hrW : r = (r ᵥ* C) ᵥ* (U + V * mat g₀) := by
    rw [Matrix.vecMul_vecMul, hCW, Matrix.vecMul_one]
  obtain ⟨b, hb⟩ : ∃ b : Fin N → L, b = fun i => -σ (r i.rev) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : L, w = r ⬝ᵥ ((C * V * mat g₀) *ᵥ b) := ⟨_, rfl⟩
  obtain ⟨xx, hxx⟩ : ∃ xx : L, xx = r ⬝ᵥ b - w - σ w := ⟨_, rfl⟩
  have hb' : b = -(dv σ r) := by
    rw [hb]
    ext i
    simp [dv]
  have e1 : r ⬝ᵥ b = -(H σ r 1 r) := by
    unfold H
    rw [hb', Matrix.one_mulVec, dotProduct_neg]
  have e2 : w = -(H σ r (C * V * mat g₀) r) := by
    unfold H
    rw [hw, hb', Matrix.mulVec_neg, dotProduct_neg]
  have e3 : σ w = -(H σ r (st σ (C * V * mat g₀)) r) := by
    rw [e2, map_neg, H_conj σ hσ]
  have key : xx = H σ (r ᵥ* C) (-(U * st σ U) + V * st σ V) (r ᵥ* C) := by
    rw [hxx, e1, e3, e2, ← defect_eq g₀ hWC, H_add, H_add, H_neg, ← H_vecMul, ← H_vecMul, ← H_vecMul, ← hrW]
    ring
  have hM : GlobalTheory.InertZeta.IsInt (-(U * st σ U) + V * st σ V) := by
    refine GlobalTheory.InertZeta.IsInt.add ?_ (GlobalTheory.InertZeta.IsInt.mul hVi (isInt_st hv hVi))
    intro i j
    rw [Matrix.neg_apply]
    exact Subring.neg_mem _ (GlobalTheory.InertZeta.IsInt.mul hUi (isInt_st hv hUi) i j)
  have hint : ϖ ^ (2 * e) * xx ∈ intL L := by
    have ht : σ (ϖ ^ e) = ϖ ^ e := by rw [map_pow, hϖ]
    have h2 : ϖ ^ (2 * e) * xx
        = H σ (ϖ ^ e • (r ᵥ* C)) (-(U * st σ U) + V * st σ V) (ϖ ^ e • (r ᵥ* C)) := by
      rw [H_smul σ _ _ ht, key, two_mul, pow_add]
    rw [h2]
    refine H_mem hv hM (fun j => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    exact hr j
  have hϖint : ϖ ∈ intL L := by
    simp only [Formalism.UG.intL, Valuation.mem_integer_iff]
    rw [hϖv, ← WithZero.coe_one, WithZero.coe_le_coe]
    exact (Multiplicative.ofAdd_le (a := (-1 : ℤ)) (b := 0)).mpr (by norm_num)
  have hσxx : σ xx = xx := by
    rw [hxx, map_sub, map_sub, hσ, e1, map_neg, H_conj σ hσ, st_one]
    ring
  have hsum : r ⬝ᵥ b = -∑ j, r j * σ (r j.rev) := by
    rw [hb]
    simp [dotProduct, Finset.sum_neg_distrib]
  have hc : (w + xx * τ) + σ (w + xx * τ) = -∑ j, r j * σ (r j.rev) := by
    rw [← hsum, map_add, map_mul, hσxx]
    have hrb : r ⬝ᵥ b = xx + w + σ w := by rw [hxx]; ring
    rw [hrb]
    linear_combination xx * hτ1
  obtain ⟨u, hu, hrow, hcorner⟩ := h3 r (w + xx * τ) hc
  obtain ⟨hrc, -, -⟩ := h1 u hu
  have hcol : colOf u = b := by
    funext i
    have h := hrc i.rev
    rw [Fin.rev_rev, hrow] at h
    rw [hb]
    calc colOf u i = σ (σ (colOf u i)) := (hσ _).symm
      _ = σ (-(r i.rev)) := by rw [h, neg_neg]
      _ = -σ (r i.rev) := map_neg _ _
  refine ⟨u, hu, hrow, ?_⟩
  unfold GlobalTheory.InertZeta.Small
  refine ⟨?_, ?_⟩
  · rw [hrow]
    exact hr
  · rw [hcorner, hrow, hcol, ← hw]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hef
    rw [show w + xx * τ - w = xx * τ by ring, pow_add,
      show ϖ ^ (2 * e) * ϖ ^ d * (xx * τ) = (ϖ ^ (2 * e) * xx) * (ϖ ^ d * τ) by ring]
    exact Subring.mul_mem _ hint (Subring.mul_mem _ (Subring.pow_mem _ hϖint d) hτ)

end GlobalTheory.CompanionTheory.InertCorner
