import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalJacobianOfDoubleCoset

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.WFL Formalism.QuantumDeterminants Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

section Forms

variable {n : ℕ}

theorem hJ_add_l (ε : Fin n → Bool) (x y w : Fin n → ℂ) : hJ ε (x + y) w = hJ ε x w + hJ ε y w := by
  simp only [hJ, star_add, add_dotProduct]

theorem hJ_add_r (ε : Fin n → Bool) (x y w : Fin n → ℂ) : hJ ε w (x + y) = hJ ε w x + hJ ε w y := by
  simp only [hJ, mulVec_add, dotProduct_add]

theorem hJ_sub_l (ε : Fin n → Bool) (x y w : Fin n → ℂ) : hJ ε (x - y) w = hJ ε x w - hJ ε y w := by
  simp only [hJ, star_sub, sub_dotProduct]

theorem hJ_sub_r (ε : Fin n → Bool) (x y w : Fin n → ℂ) : hJ ε w (x - y) = hJ ε w x - hJ ε w y := by
  simp only [hJ, mulVec_sub, dotProduct_sub]

theorem hJ_sum_l {ι : Type*} [Fintype ι] (ε : Fin n → Bool) (x : ι → ℂ) (u : ι → Fin n → ℂ) (w : Fin n → ℂ) :
    hJ ε (∑ i, x i • u i) w = ∑ i, conj (x i) * hJ ε (u i) w := by
  simp only [hJ, star_sum, star_smul, sum_dotProduct, smul_dotProduct, smul_eq_mul, Complex.star_def]

theorem hJ_sum_r {ι : Type*} [Fintype ι] (ε : Fin n → Bool) (y : ι → ℂ) (v : ι → Fin n → ℂ) (w : Fin n → ℂ) :
    hJ ε w (∑ j, y j • v j) = ∑ j, y j * hJ ε w (v j) := by
  simp only [hJ, mulVec_sum, dotProduct_sum, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hJ_comb_self {ι : Type*} [Fintype ι] [DecidableEq ι] (ε : Fin n → Bool) (x : ι → ℂ) (u : ι → Fin n → ℂ)
    (d : ι → ℝ) (hu : ∀ i j, hJ ε (u i) (u j) = if i = j then (d i : ℂ) else 0) :
    hJ ε (∑ i, x i • u i) (∑ i, x i • u i) = ((∑ i, d i * Complex.normSq (x i) : ℝ) : ℂ) := by
  rw [hJ_sum_l]
  simp only [hJ_sum_r, hu, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  ring

theorem card_le_of_signs {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (ε : Fin n → Bool)
    (u : ι → Fin n → ℂ) (dp : ι → ℝ) (hdp : ∀ i, 0 < dp i)
    (hu : ∀ i j, hJ ε (u i) (u j) = if i = j then (dp i : ℂ) else 0)
    (v : κ → Fin n → ℂ) (dn : κ → ℝ) (hdn : ∀ i, dn i < 0)
    (hv : ∀ i j, hJ ε (v i) (v j) = if i = j then (dn i : ℂ) else 0) :
    Fintype.card ι + Fintype.card κ ≤ n := by
  have hli : LinearIndependent ℂ (Sum.elim u v) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [Sum.elim_inl, Sum.elim_inr] at hg
    set x := ∑ i, g (Sum.inl i) • u i with hx
    set y := ∑ j, g (Sum.inr j) • v j with hy
    have hxy : x = -y := eq_neg_of_add_eq_zero_left hg
    have h1 : hJ ε x x = ((∑ i, dp i * Complex.normSq (g (Sum.inl i)) : ℝ) : ℂ) :=
      hJ_comb_self ε (fun i => g (Sum.inl i)) u dp hu
    have h2 : hJ ε y y = ((∑ j, dn j * Complex.normSq (g (Sum.inr j)) : ℝ) : ℂ) :=
      hJ_comb_self ε (fun j => g (Sum.inr j)) v dn hv
    have h3 : hJ ε x x = hJ ε y y := by
      rw [hxy]
      simp [hJ, Matrix.mulVec_neg]
    rw [h1, h2] at h3
    have h4 : (∑ i, dp i * Complex.normSq (g (Sum.inl i))) =
        ∑ j, dn j * Complex.normSq (g (Sum.inr j)) := by exact_mod_cast h3
    have hA : 0 ≤ ∑ i, dp i * Complex.normSq (g (Sum.inl i)) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hdp i).le (Complex.normSq_nonneg _)
    have hB : ∑ j, dn j * Complex.normSq (g (Sum.inr j)) ≤ 0 :=
      Finset.sum_nonpos fun j _ => mul_nonpos_of_nonpos_of_nonneg (hdn j).le (Complex.normSq_nonneg _)
    have hA0 : ∑ i, dp i * Complex.normSq (g (Sum.inl i)) = 0 := by linarith
    have hB0 : ∑ j, dn j * Complex.normSq (g (Sum.inr j)) = 0 := by linarith
    rintro (i | j)
    · have h5 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => mul_nonneg (hdp i).le (Complex.normSq_nonneg (g (Sum.inl i))))).mp hA0 i
        (Finset.mem_univ _)
      rcases mul_eq_zero.mp h5 with h | h
      · exact absurd h (hdp i).ne'
      · exact Complex.normSq_eq_zero.mp h
    · have h5 := (Finset.sum_eq_zero_iff_of_nonpos
        (fun j _ => mul_nonpos_of_nonpos_of_nonneg (hdn j).le (Complex.normSq_nonneg (g (Sum.inr j))))).mp
        hB0 j (Finset.mem_univ _)
      rcases mul_eq_zero.mp h5 with h | h
      · exact absurd h (hdn j).ne
      · exact Complex.normSq_eq_zero.mp h
  have h := hli.fintype_card_le_finrank
  simpa [Fintype.card_sum, Module.finrank_fin_fun] using h

theorem hJ_bvec (ε : Fin n → Bool) (i j : Fin n) :
    hJ ε (bvec i) (bvec j) = if i = j then (if ε i then 1 else -1) else 0 := by
  unfold hJ bvec Formalism.REAL.Jm
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Pi.single_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem hJ_bvec_sub (ε : Fin n → Bool) (s : Bool) (i j : {i // ε i = s}) :
    hJ ε (bvec i.1) (bvec j.1) = if i = j then ((if s then 1 else -1 : ℝ) : ℂ) else 0 := by
  rw [hJ_bvec]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl, i.2]
    cases s <;> simp
  · rw [if_neg (fun h' => h (Subtype.ext h')), if_neg h]

end Forms

section Sig

variable {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}

def posF (e f : Fin r → Fin (2 * r + k + 1) → ℂ) (wf : Fin k → Fin (2 * r + k + 1) → ℂ) :
    Fin r ⊕ Fin k → Fin (2 * r + k + 1) → ℂ
  | Sum.inl a => e a + f a
  | Sum.inr c => wf c

def negF (e f : Fin r → Fin (2 * r + k + 1) → ℂ) (z0 : Fin (2 * r + k + 1) → ℂ) :
    Fin r ⊕ Unit → Fin (2 * r + k + 1) → ℂ
  | Sum.inl a => e a - f a
  | Sum.inr _ => z0

theorem hJ_fe (hF : IsFrameJ ε e f wf z0) (a b : Fin r) : hJ ε (f a) (e b) = if a = b then 1 else 0 := by
  have hs : ∀ x y : Fin (2 * r + k + 1) → ℂ, hJ ε y x = conj (hJ ε x y) := by
    intro x y
    simp only [hJ, dotProduct, Formalism.REAL.Jm, mulVec_diagonal, map_sum, map_mul, Pi.star_apply,
      Complex.star_def, Complex.conj_conj]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp <;> ring
  rw [hs, hF.ef b a]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

theorem posF_gram (hF : IsFrameJ ε e f wf z0) (i j : Fin r ⊕ Fin k) :
    hJ ε (posF e f wf i) (posF e f wf j) =
      if i = j then (((Sum.elim (fun _ => (2 : ℝ)) (fun _ => (1 : ℝ))) i : ℝ) : ℂ) else 0 := by
  have hs : ∀ x y : Fin (2 * r + k + 1) → ℂ, hJ ε y x = conj (hJ ε x y) := by
    intro x y
    simp only [hJ, dotProduct, Formalism.REAL.Jm, mulVec_diagonal, map_sum, map_mul, Pi.star_apply,
      Complex.star_def, Complex.conj_conj]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp <;> ring
  rcases i with a | c <;> rcases j with b | d
  · simp only [posF, hJ_add_l, hJ_add_r, hF.ee, hF.ff, hF.ef, hJ_fe hF, Sum.inl.injEq]
    by_cases h : a = b
    · subst h; simp; norm_num
    · simp [h]
  · simp [posF, hJ_add_l, hF.ew, hF.fw]
  · simp [posF, hJ_add_r, hs (e _) (wf c), hs (f _) (wf c), hF.ew, hF.fw]
  · simp only [posF, hF.ww, Sum.inr.injEq]
    by_cases h : c = d
    · subst h; simp
    · simp [h]

theorem negF_gram (hF : IsFrameJ ε e f wf z0) (i j : Fin r ⊕ Unit) :
    hJ ε (negF e f z0 i) (negF e f z0 j) =
      if i = j then (((Sum.elim (fun _ => (-2 : ℝ)) (fun _ => (-1 : ℝ))) i : ℝ) : ℂ) else 0 := by
  have hs : ∀ x y : Fin (2 * r + k + 1) → ℂ, hJ ε y x = conj (hJ ε x y) := by
    intro x y
    simp only [hJ, dotProduct, Formalism.REAL.Jm, mulVec_diagonal, map_sum, map_mul, Pi.star_apply,
      Complex.star_def, Complex.conj_conj]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp <;> ring
  rcases i with a | u <;> rcases j with b | w
  · simp only [negF, hJ_sub_l, hJ_sub_r, hF.ee, hF.ff, hF.ef, hJ_fe hF, Sum.inl.injEq]
    by_cases h : a = b
    · subst h; simp; norm_num
    · simp [h]
  · simp [negF, hJ_sub_l, hF.ez, hF.fz]
  · simp [negF, hJ_sub_r, hs (e _) z0, hs (f _) z0, hF.ez, hF.fz]
  · simp [negF, hF.zz]

theorem sig_of_frame (hF : IsFrameJ ε e f wf z0) :
    (Finset.univ.filter (fun i => ε i = false)).card = r + 1 := by
  have h1 := card_le_of_signs ε (posF e f wf) (Sum.elim (fun _ => (2 : ℝ)) (fun _ => (1 : ℝ)))
    (by rintro (_ | _) <;> norm_num) (posF_gram hF)
    (fun i : {i // ε i = false} => bvec i.1) (fun _ => (-1 : ℝ)) (fun _ => by norm_num)
    (by intro i j; rw [hJ_bvec_sub]; simp)
  have h2 := card_le_of_signs ε (fun i : {i // ε i = true} => bvec i.1) (fun _ => (1 : ℝ))
    (fun _ => by norm_num) (by intro i j; rw [hJ_bvec_sub]; simp)
    (negF e f z0) (Sum.elim (fun _ => (-2 : ℝ)) (fun _ => (-1 : ℝ)))
    (by rintro (_ | _) <;> norm_num) (negF_gram hF)
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit, Fintype.card_subtype] at h1 h2
  have h3 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2 * r + k + 1))))
    (fun i => ε i = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h3
  omega

theorem hJ_Qm_self (hF : IsFrameJ ε e f wf z0) (zB : Fin (2 * r + k + 1) → ℂ) :
    hJ ε (Qm e f wf z0 *ᵥ zB) (Qm e f wf z0 *ᵥ zB) = -((Tz k r zB : ℝ) : ℂ) := by
  have hs : ∀ x y : Fin (2 * r + k + 1) → ℂ, hJ ε y x = conj (hJ ε x y) := by
    intro x y
    simp only [hJ, dotProduct, Formalism.REAL.Jm, mulVec_diagonal, map_sum, map_mul, Pi.star_apply,
      Complex.star_def, Complex.conj_conj]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp <;> ring
  have hc1 : ∀ j : Fin (2 * r + k + 1), (hj : j.val < r) → colQ e f wf z0 j = e ⟨j.val, hj⟩ := by
    intro j hj; unfold colQ; rw [dif_pos hj]
  have hc2 : ∀ j : Fin (2 * r + k + 1), (h1 : r ≤ j.val) → (h2 : j.val < r + k) →
      colQ e f wf z0 j = wf ⟨j.val - r, by omega⟩ := by
    intro j h1 h2; unfold colQ; rw [dif_neg (by omega), dif_pos h2]
  have hc3 : ∀ j : Fin (2 * r + k + 1), j.val = r + k → colQ e f wf z0 j = z0 := by
    intro j h; unfold colQ; rw [dif_neg (by omega), dif_neg (by omega), dif_pos h]
  have hc4 : ∀ j : Fin (2 * r + k + 1), (h : r + k < j.val) →
      colQ e f wf z0 j = f ⟨2 * r + k - j.val, by omega⟩ := by
    intro j h; unfold colQ; rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
  have hQ : ∀ v : Fin (2 * r + k + 1) → ℂ, Qm e f wf z0 *ᵥ v = ∑ j, v j • colQ e f wf z0 j := by
    intro v; ext i; simp [Qm, mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hwe : ∀ c a, hJ ε (wf c) (e a) = 0 := fun c a => by rw [hs, hF.ew]; simp
  have hwf : ∀ c a, hJ ε (wf c) (f a) = 0 := fun c a => by rw [hs, hF.fw]; simp
  have hze : ∀ a, hJ ε z0 (e a) = 0 := fun a => by rw [hs, hF.ez]; simp
  have hzf : ∀ a, hJ ε z0 (f a) = 0 := fun a => by rw [hs, hF.fz]; simp
  have hwz : ∀ c, hJ ε (wf c) z0 = 0 := fun c => by rw [hs, hF.zw]; simp
  have hG : ∀ i j : Fin (2 * r + k + 1),
      hJ ε (colQ e f wf z0 i) (colQ e f wf z0 j) = Hpk k r i j := by
    intro i j
    have hH : Hpk k r i j = if i.val < r ∧ i.val + j.val = 2 * r + k then 1
        else if j.val < r ∧ i.val + j.val = 2 * r + k then 1
        else if r ≤ i.val ∧ i.val ≤ r + k ∧ i = j then (if i.val = r + k then -1 else 1) else 0 := rfl
    rw [hH]
    have h4 : ∀ m : Fin (2 * r + k + 1),
        m.val < r ∨ (r ≤ m.val ∧ m.val < r + k) ∨ m.val = r + k ∨ r + k < m.val := by
      intro m; omega
    rcases h4 i with hi | ⟨hi1, hi2⟩ | hi | hi <;> rcases h4 j with hj | ⟨hj1, hj2⟩ | hj | hj
    all_goals first | rw [hc1 i hi] | rw [hc2 i hi1 hi2] | rw [hc3 i hi] | rw [hc4 i hi]
    all_goals first | rw [hc1 j hj] | rw [hc2 j hj1 hj2] | rw [hc3 j hj] | rw [hc4 j hj]
    all_goals simp only [hF.ee, hF.ff, hF.ef, hJ_fe hF, hF.ew, hF.fw, hF.ww, hF.ez, hF.fz, hF.zz, hF.zw,
      hwe, hwf, hze, hzf, hwz, Fin.ext_iff, Fin.mk.injEq]
    all_goals split_ifs <;> first | rfl | (exfalso; omega) | norm_num | omega
  have hX : hJ ε (Qm e f wf z0 *ᵥ zB) (Qm e f wf z0 *ᵥ zB) = herm (Hpk k r) zB zB := by
    rw [hQ, hJ_sum_l]
    simp only [hJ_sum_r, hG, herm, dotProduct, mulVec, Pi.star_apply, Complex.star_def, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hreal : conj (hJ ε (Qm e f wf z0 *ᵥ zB) (Qm e f wf z0 *ᵥ zB)) =
      hJ ε (Qm e f wf z0 *ᵥ zB) (Qm e f wf z0 *ᵥ zB) := (hs _ _).symm
  rw [show -((Tz k r zB : ℝ) : ℂ) = ((herm (Hpk k r) zB zB).re : ℂ) by simp [Tz], ← hX]
  exact (Complex.conj_eq_iff_re.mp hreal).symm

theorem hJ_e_Qm (hF : IsFrameJ ε e f wf z0) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (a : Fin r) :
    hJ ε (e a) (Qm e f wf z0 *ᵥ v) = 0 := by
  have hc1 : ∀ j : Fin (2 * r + k + 1), (hj : j.val < r) → colQ e f wf z0 j = e ⟨j.val, hj⟩ := by
    intro j hj; unfold colQ; rw [dif_pos hj]
  have hc2 : ∀ j : Fin (2 * r + k + 1), (h1 : r ≤ j.val) → (h2 : j.val < r + k) →
      colQ e f wf z0 j = wf ⟨j.val - r, by omega⟩ := by
    intro j h1 h2; unfold colQ; rw [dif_neg (by omega), dif_pos h2]
  have hc3 : ∀ j : Fin (2 * r + k + 1), j.val = r + k → colQ e f wf z0 j = z0 := by
    intro j h; unfold colQ; rw [dif_neg (by omega), dif_neg (by omega), dif_pos h]
  have hc4 : ∀ j : Fin (2 * r + k + 1), (h : r + k < j.val) →
      colQ e f wf z0 j = f ⟨2 * r + k - j.val, by omega⟩ := by
    intro j h; unfold colQ; rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
  have hQ : ∀ v : Fin (2 * r + k + 1) → ℂ, Qm e f wf z0 *ᵥ v = ∑ j, v j • colQ e f wf z0 j := by
    intro v; ext i; simp [Qm, mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [hQ, hJ_sum_r]
  refine Finset.sum_eq_zero fun j _ => ?_
  rcases lt_or_ge j.val r with h1 | h1
  · rw [hv j (Or.inl h1)]; simp
  rcases lt_or_ge j.val (r + k) with h2 | h2
  · rw [hc2 j h1 h2, hF.ew]; simp
  rcases eq_or_lt_of_le h2 with h3 | h3
  · rw [hc3 j h3.symm, hF.ez]; simp
  · rw [hv j (Or.inr h3)]; simp

theorem e_li (hF : IsFrameJ ε e f wf z0) : LinearIndependent ℂ e := by
  rw [Fintype.linearIndependent_iff]
  intro c hc b
  have h := congrArg (fun v => hJ ε v (f b)) hc
  simp only [hJ_sum_l, hF.ef, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true] at h
  simpa [hJ] using h

theorem frameX_of (hF : IsFrameJ ε e f wf z0) (hk : 1 ≤ k) {zB zB' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r zB)
    (hz' : inWb k r zB') (hT : 0 < Tz k r zB) (hT' : 0 < Tz k r zB') :
    FrameLoc ε k e (Qm e f wf z0 *ᵥ zB) (Qm e f wf z0 *ᵥ zB') (Tz k r zB) (Tz k r zB') where
  dim := by omega
  k_pos := hk
  sig := sig_of_frame hF
  e_li := e_li hF
  ee := hF.ee
  ez := hJ_e_Qm hF hz
  ez' := hJ_e_Qm hF hz'
  zz := hJ_Qm_self hF zB
  zz' := hJ_Qm_self hF zB'
  T_pos := hT
  T'_pos := hT'

end Sig

end Formalism.L2.SG.Pf.NcReal.JX
