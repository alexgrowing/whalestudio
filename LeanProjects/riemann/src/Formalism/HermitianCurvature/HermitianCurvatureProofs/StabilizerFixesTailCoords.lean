import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfSmoothBuiltOfLeaves
import Formalism.PeriodIntegrals.ContinuousExpLie

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity.LieSplitPf

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def pw (k r : ℕ) : Fin (2 * r + k + 1) → ℂ := fun i => if r ≤ i.val ∧ i.val ≤ r + k then 1 else 0

def aP (X : PI.Mx k r) : PI.Mx k r := Matrix.diagonal (pw k r) * X * Matrix.diagonal (pw k r)

theorem middleBlock_apply (X : PI.Mx k r) (i j : Fin (2 * r + k + 1)) : aP X i j = pw k r i * X i j * pw k r j := by
  unfold aP
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem clm_zero (X : PI.Mx k r) (L : PI.Mx k r →L[ℝ] ℂ) (c : ℂ)
    (h : ∀ t : ℝ, L (NormedSpace.exp ((t : ℂ) • X)) = c) : L X = 0 := by
  have h1 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (PI.exp_deriv X)
  have h2 : HasDerivAt (fun t : ℝ => L (NormedSpace.exp ((t : ℂ) • X))) 0 0 := by
    have : (fun t : ℝ => L (NormedSpace.exp ((t : ℂ) • X))) = fun _ => c := funext h
    rw [this]; exact hasDerivAt_const _ _
  exact h1.unique h2

def mvL (v : Fin (2 * r + k + 1) → ℂ) : PI.Mx k r →L[ℂ] (Fin (2 * r + k + 1) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M *ᵥ v
      map_add' := fun M N => Matrix.add_mulVec M N v
      map_smul' := fun c M => by
        funext i
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] }

theorem mvL_apply (v : Fin (2 * r + k + 1) → ℂ) (M : PI.Mx k r) : mvL v M = M *ᵥ v := rfl

theorem exp_fix (A : PI.Mx k r) (v : Fin (2 * r + k + 1) → ℂ) (hv : A *ᵥ v = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • A) *ᵥ v = v := by
  have hz : ∀ n : ℕ, ((t : ℂ) • A) ^ (n + 1) *ᵥ v = 0 := by
    intro n
    have hv' : ((t : ℂ) • A) *ᵥ v = 0 := by
      funext i
      have := congrFun hv i
      simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
      simp only [mul_assoc, ← Finset.mul_sum, this, mul_zero]
    rw [pow_succ, ← Matrix.mulVec_mulVec, hv', Matrix.mulVec_zero]
  have h1 : HasSum (fun n : ℕ => mvL v (((n.factorial : ℂ)⁻¹) • ((t : ℂ) • A) ^ n))
      (mvL v (NormedSpace.exp ((t : ℂ) • A))) := by
    open scoped Matrix.Norms.Operator in
    exact (mvL v).hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((t : ℂ) • A))
  have h2 : HasSum (fun n : ℕ => mvL v (((n.factorial : ℂ)⁻¹) • ((t : ℂ) • A) ^ n))
      (mvL v (((Nat.factorial 0 : ℂ)⁻¹) • ((t : ℂ) • A) ^ 0)) := by
    apply hasSum_single 0
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [map_smul, mvL_apply, hz m, smul_zero]
  have := h1.unique h2
  rw [mvL_apply, mvL_apply] at this
  rw [this]
  simp

theorem hcol {z : Fin (2 * r + k + 1) → ℂ} {h : PI.Mx k r} (hh : h ∈ Formalism.QuantumDeterminants.UWset k r z)
    (i l : Fin (2 * r + k + 1)) (hl : l.val < r) : h i l = if i = l then 1 else 0 := by
  have he : Formalism.QuantumDeterminants.eI k r ⟨l.val, hl⟩ = l := Fin.ext rfl
  have := congrFun (hh.2.1 ⟨l.val, hl⟩).1 i
  rw [he] at this
  simpa [Formalism.QuantumDeterminants.bvec, Matrix.mulVec, dotProduct, Pi.single_apply] using this

theorem S_col {z : Fin (2 * r + k + 1) → ℂ} {s : PI.Mx k r} (hs : s ∈ Formalism.QuantumDeterminants.Sset k r z) (a : Fin r)
    (i : Fin (2 * r + k + 1)) (hai : a.val ≤ i.val) :
    s i (Formalism.QuantumDeterminants.eI k r a) = if i = Formalism.QuantumDeterminants.eI k r a then 1 else 0 := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  have ha := a.2
  rw [Matrix.mul_apply, Finset.sum_eq_single (Formalism.QuantumDeterminants.eI k r a)]
  · rw [hm.2.1 a (Formalism.QuantumDeterminants.eI k r a) le_rfl, if_pos rfl, mul_one]
    exact hcol hh i _ a.2
  · intro l _ hl
    by_cases hal : a.val ≤ l.val
    · rw [hm.2.1 a l hal, if_neg hl, mul_zero]
    · rw [hcol hh i l (by omega), if_neg (by intro e; rw [e] at hai; omega), zero_mul]
  · intro hn; exact absurd (Finset.mem_univ _) hn

theorem stabilizer_fixes_tail_coords {z : Fin (2 * r + k + 1) → ℂ} (hz : Formalism.QuantumDeterminants.inWb k r z) {s : PI.Mx k r}
    (hs : s ∈ Formalism.QuantumDeterminants.Sset k r z) (i : Fin (2 * r + k + 1)) (hi : r ≤ i.val) : (s *ᵥ z) i = z i := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  rw [← Matrix.mulVec_mulVec]
  have hv : ∀ l : Fin (2 * r + k + 1), r ≤ l.val → (m *ᵥ z) l = z l := by
    intro l hl
    change (∑ x, m l x * z x) = z l
    rw [Finset.sum_eq_single l]
    · by_cases hlW : l.val ≤ r + k
      · rw [hm.2.2 l l hl hlW hl, if_pos rfl, one_mul]
      · rw [hz l (Or.inr (by omega)), mul_zero]
    · intro x _ hx
      by_cases hxW : r ≤ x.val ∧ x.val ≤ r + k
      · rw [hm.2.2 l x hxW.1 hxW.2 hl, if_neg (fun e => hx e.symm), zero_mul]
      · rw [hz x (by omega), mul_zero]
    · intro hn; exact absurd (Finset.mem_univ _) hn
  have hz' : (∑ l, h i l * z l) = z i := congrFun hh.2.2 i
  change (∑ l, h i l * (m *ᵥ z) l) = z i
  rw [← hz']
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : r ≤ l.val
  · rw [hv l hl]
  · rw [hcol hh i l (by omega), if_neg (by intro e; rw [e] at hi; omega), zero_mul, zero_mul]

theorem lieHpk_of {X : PI.Mx k r}
    (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : PI.InLieHpk k r X := by
  have hH2 := (Formalism.QuantumDeterminants.hpkFacts k r).2.1
  have hf : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Xᴴ)) Xᴴ 0 := PI.exp_deriv _
  have hg : HasDerivAt (fun t : ℝ => Formalism.QuantumDeterminants.Hpk k r * NormedSpace.exp ((t : ℂ) • (-X)) * Formalism.QuantumDeterminants.Hpk k r)
      (Formalism.QuantumDeterminants.Hpk k r * (-X) * Formalism.QuantumDeterminants.Hpk k r) 0 :=
    (PI.mulR (Formalism.QuantumDeterminants.Hpk k r)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((PI.mulL (Formalism.QuantumDeterminants.Hpk k r)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (PI.exp_deriv (-X)))
  have hfg : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Xᴴ)) =
      fun t : ℝ => Formalism.QuantumDeterminants.Hpk k r * NormedSpace.exp ((t : ℂ) • (-X)) * Formalism.QuantumDeterminants.Hpk k r := by
    funext t
    have hU : (NormedSpace.exp ((t : ℂ) • X))ᴴ * Formalism.QuantumDeterminants.Hpk k r * NormedSpace.exp ((t : ℂ) • X) =
        Formalism.QuantumDeterminants.Hpk k r := hX t
    have hst : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hst] at hU
    have e2 : NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((t : ℂ) • (-X)) = 1 := by
      rw [smul_neg, ← Matrix.exp_add_of_commute _ _ ((Commute.refl ((t : ℂ) • X)).neg_right)]
      simp
    calc NormedSpace.exp ((t : ℂ) • Xᴴ)
        = NormedSpace.exp ((t : ℂ) • Xᴴ) * Formalism.QuantumDeterminants.Hpk k r *
            (NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((t : ℂ) • (-X))) * Formalism.QuantumDeterminants.Hpk k r := by
          rw [e2, Matrix.mul_one, Matrix.mul_assoc, hH2, Matrix.mul_one]
      _ = (NormedSpace.exp ((t : ℂ) • Xᴴ) * Formalism.QuantumDeterminants.Hpk k r * NormedSpace.exp ((t : ℂ) • X)) *
            NormedSpace.exp ((t : ℂ) • (-X)) * Formalism.QuantumDeterminants.Hpk k r := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU]
  rw [hfg] at hf
  have e := hf.unique hg
  show Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X = 0
  rw [e, Matrix.mul_assoc, hH2]
  simp

theorem hpk_row (a : Fin r) (l : Fin (2 * r + k + 1)) :
    Formalism.QuantumDeterminants.Hpk k r (Formalism.QuantumDeterminants.eI k r a) l = if a.val + l.val = 2 * r + k then 1 else 0 := by
  have ha := a.2
  have hl := l.2
  simp only [Formalism.QuantumDeterminants.Hpk, Formalism.QuantumDeterminants.eI, Fin.val_mk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_cross (i j : Fin (2 * r + k + 1))
    (h : (r ≤ i.val ∧ i.val ≤ r + k ∧ (j.val < r ∨ r + k < j.val)) ∨
      ((i.val < r ∨ r + k < i.val) ∧ r ≤ j.val ∧ j.val ≤ r + k)) : Formalism.QuantumDeterminants.Hpk k r i j = 0 := by
  have hi := i.2
  have hj := j.2
  simp only [Formalism.QuantumDeterminants.Hpk]
  split_ifs with h1 h2 h3 <;> (try rfl) <;> (exfalso; omega)

theorem hpk_pw : Formalism.QuantumDeterminants.Hpk k r * Matrix.diagonal (pw k r) = Matrix.diagonal (pw k r) * Formalism.QuantumDeterminants.Hpk k r := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  unfold pw
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k <;> by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
  · simp [hi, hj]
  · rw [hpk_cross i j (Or.inl ⟨hi.1, hi.2, by omega⟩)]; simp
  · rw [hpk_cross i j (Or.inr ⟨by omega, hj.1, hj.2⟩)]; simp
  · simp [hi, hj]

theorem pw_star : (Matrix.diagonal (pw k r))ᴴ = Matrix.diagonal (pw k r) := by
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  by_cases h : r ≤ i.val ∧ i.val ≤ r + k <;> simp [pw, h]

theorem inLie_aP {X : PI.Mx k r} (hX : PI.InLieHpk k r X) : PI.InLieHpk k r (aP X) := by
  have hX' : Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X = 0 := hX
  show (aP X)ᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * aP X = 0
  unfold aP
  set P := Matrix.diagonal (pw k r)
  set H := Formalism.QuantumDeterminants.Hpk k r
  have hc : H * P = P * H := hpk_pw
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, pw_star]
  have e1 : P * (Xᴴ * P) * H = P * (Xᴴ * H) * P := by
    rw [Matrix.mul_assoc P (Xᴴ * P) H, Matrix.mul_assoc Xᴴ P H, ← hc, ← Matrix.mul_assoc Xᴴ H P,
      ← Matrix.mul_assoc P (Xᴴ * H) P]
  have e2 : H * (P * X * P) = P * (H * X) * P := by
    rw [← Matrix.mul_assoc H (P * X) P, ← Matrix.mul_assoc H P X, hc, Matrix.mul_assoc P H X]
  rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hX', Matrix.mul_zero, Matrix.zero_mul]

theorem inLie_sub {X Y : PI.Mx k r} (hX : PI.InLieHpk k r X) (hY : PI.InLieHpk k r Y) :
    PI.InLieHpk k r (X - Y) := by
  have hX' : Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X = 0 := hX
  have hY' : Yᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * Y = 0 := hY
  show (X - Y)ᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * (X - Y) = 0
  rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]
  calc Xᴴ * Formalism.QuantumDeterminants.Hpk k r - Yᴴ * Formalism.QuantumDeterminants.Hpk k r + (Formalism.QuantumDeterminants.Hpk k r * X - Formalism.QuantumDeterminants.Hpk k r * Y)
      = (Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X) - (Yᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * Y) := by
        abel
    _ = 0 := by rw [hX', hY', sub_zero]

theorem pw_mulVec_bvec (l : Fin (2 * r + k + 1)) (hl : ¬(r ≤ l.val ∧ l.val ≤ r + k)) :
    Matrix.diagonal (pw k r) *ᵥ Formalism.QuantumDeterminants.bvec l = 0 := by
  funext i
  rw [Matrix.mulVec_diagonal]
  by_cases hi : i = l
  · subst hi; simp [pw, hl]
  · simp [Formalism.QuantumDeterminants.bvec, hi]

theorem middleBlock_mulVec_basisVec_eq_zero (X : PI.Mx k r) (l : Fin (2 * r + k + 1)) (hl : ¬(r ≤ l.val ∧ l.val ≤ r + k)) :
    aP X *ᵥ Formalism.QuantumDeterminants.bvec l = 0 := by
  unfold aP
  rw [← Matrix.mulVec_mulVec, pw_mulVec_bvec l hl, Matrix.mulVec_zero]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity.LieSplitPf

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

open LieSplitPf

theorem lie_stabilizer_splitting : LieSsetSplit := by
  intro k r z hz _hT X hX
  have hXS : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Formalism.QuantumDeterminants.Sset k r z := hX
  have hUH : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    intro t
    obtain ⟨h, hh, m, hm, he⟩ := hXS t
    rw [he]; exact PI.UH_mul hh.1 hm.1
  have F0 : PI.InLieHpk k r X := lieHpk_of hUH
  have F1 : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → X i (Formalism.QuantumDeterminants.eI k r a) = 0 := by
    intro a i hai
    refine (PI.exp_entry X i _).unique ?_
    have : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i (Formalism.QuantumDeterminants.eI k r a)) =
        fun _ => if i = Formalism.QuantumDeterminants.eI k r a then 1 else 0 := funext fun t => S_col (hXS t) a i hai
    rw [this]; exact hasDerivAt_const _ _
  have F2 : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → (X *ᵥ z) i = 0 := by
    intro i hi
    exact clm_zero X ((ContinuousLinearMap.proj i).comp ((mvL z).restrictScalars ℝ)) (z i)
      (fun t => stabilizer_fixes_tail_coords hz (hXS t) i hi)
  have F3 : ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r + k < i.val → X i j = 0 := by
    intro i j h1 h2 h3
    have hi := i.2
    let a : Fin r := ⟨2 * r + k - i.val, by omega⟩
    have hE := congrFun (congrFun F0 (Formalism.QuantumDeterminants.eI k r a)) j
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.zero_apply] at hE
    have s1 : ∑ l, Xᴴ (Formalism.QuantumDeterminants.eI k r a) l * Formalism.QuantumDeterminants.Hpk k r l j = 0 := by
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : a.val ≤ l.val
      · rw [Matrix.conjTranspose_apply, F1 a l hl, star_zero, zero_mul]
      · rw [hpk_cross l j (Or.inr ⟨Or.inl (by have := a.2; omega), h1, h2⟩), mul_zero]
    have s2 : ∑ l, Formalism.QuantumDeterminants.Hpk k r (Formalism.QuantumDeterminants.eI k r a) l * X l j = X i j := by
      rw [Finset.sum_eq_single i]
      · rw [hpk_row, if_pos (by simp only [a]; omega), one_mul]
      · intro l _ hl
        rw [hpk_row, if_neg (by simp only [a]; intro e; exact hl (Fin.ext (by omega))), zero_mul]
      · intro hn; exact absurd (Finset.mem_univ _) hn
    rw [s1, s2, zero_add] at hE
    exact hE
  refine ⟨aP X, ?_, X - aP X, ?_, by abel⟩
  ·
    have hPz : Matrix.diagonal (pw k r) *ᵥ z = z := by
      funext i
      rw [Matrix.mulVec_diagonal]
      unfold pw
      split_ifs with h
      · rw [one_mul]
      · rw [hz i (by omega), zero_mul]
    have hAz : aP X *ᵥ z = 0 := by
      unfold aP
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPz]
      funext i
      rw [Matrix.mulVec_diagonal, Pi.zero_apply]
      unfold pw
      split_ifs with h
      · rw [F2 i h.1, mul_zero]
      · rw [zero_mul]
    intro t
    refine ⟨PI.exp_mem_UH (inLie_aP F0) t, fun a => ⟨?_, ?_⟩, exp_fix _ z hAz t⟩
    · exact exp_fix _ _ (middleBlock_mulVec_basisVec_eq_zero X _ (by have := a.2; simp only [Formalism.QuantumDeterminants.eI]; omega)) t
    · exact exp_fix _ _ (middleBlock_mulVec_basisVec_eq_zero X _ (by have := a.2; simp only [Formalism.QuantumDeterminants.esI]; omega)) t
  ·
    have hN : PI.InLieN k r (X - aP X) := by
      refine ⟨inLie_sub F0 (inLie_aP F0), ?_, ?_⟩
      · intro a i hai
        have ha := a.2
        rw [Matrix.sub_apply, middleBlock_apply, F1 a i hai]
        have : pw k r (Formalism.QuantumDeterminants.eI k r a) = 0 := by
          unfold pw; rw [if_neg]; simp only [Formalism.QuantumDeterminants.eI]; omega
        rw [this, mul_zero, sub_zero]
      · intro i j h1 h2 h3
        rw [Matrix.sub_apply, middleBlock_apply]
        have hj : pw k r j = 1 := by unfold pw; rw [if_pos ⟨h1, h2⟩]
        rw [hj, mul_one]
        by_cases hi : i.val ≤ r + k
        · have : pw k r i = 1 := by unfold pw; rw [if_pos ⟨h3, hi⟩]
          rw [this, one_mul, sub_self]
        · rw [F3 i j h1 h2 (by omega), mul_zero, sub_zero]
    intro t
    exact PI.exp_mem_N (hN.smul t)

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
