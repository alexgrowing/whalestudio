import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsEmbeddingCongrIntegralCharacterStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RingHomEqOfCongruentIntegralUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenvectorOfGeneralizedEigenUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralCharacterGeneralizedEigenStatement

open scoped BigOperators
open Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.IdemRange

section Val

variable {C : Type} [Field C] {V : VF C}

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  V.v.map_lt_add ha hb

theorem mm_neg {a : C} (ha : V.MM a) : V.MM (-a) := by
  unfold VF.MM; rw [V.v.map_neg]; exact ha

theorem mm_mul {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  unfold VF.MM; rw [V.v.map_mul]
  have hb' : (0 : WithTop ℝ) ≤ V.v b := by simpa [VF.Ge] using hb
  exact lt_of_lt_of_le ha (le_add_of_nonneg_right hb')

theorem mm_or {a b : C} (h : V.MM (a * b)) : V.MM a ∨ V.MM b := by
  unfold VF.MM at *
  rw [V.v.map_mul] at h
  by_contra hc
  rw [not_or, not_lt, not_lt] at hc
  exact absurd h (not_lt.mpr (add_nonpos hc.1 hc.2))

theorem not_mm_one : ¬ V.MM (1 : C) := by
  unfold VF.MM; rw [V.v.map_one]; exact lt_irrefl _

theorem mm_l : V.MM (V.l : C) := by
  unfold VF.MM; rw [V.v_l]; exact zero_lt_one

theorem mm_pow_sub {a b : C} (h : V.MM (a - b)) (ha : V.Ge 0 a) (hb : V.Ge 0 b) (n : ℕ) :
    V.MM (a ^ n - b ^ n) := by
  induction n with
  | zero => simp [VF.MM]
  | succ n ih =>
    have : a ^ (n + 1) - b ^ (n + 1) = (a ^ n - b ^ n) * a + (a - b) * b ^ n := by ring
    rw [this]
    exact mm_add (mm_mul ih ha) (mm_mul h (hb.pow n))

theorem eq_zero_of_ge_all {a : C} (h : ∀ N : ℕ, V.Ge N a) : a = 0 := by
  rw [← V.v.top_iff]
  unfold VF.Ge at h
  induction hv : V.v a using WithTop.recTopCoe with
  | top => rfl
  | coe t =>
    exfalso
    obtain ⟨N, hN⟩ := exists_nat_gt t
    have h1 := h N
    rw [hv] at h1
    have : (N : ℝ) ≤ t := by exact_mod_cast h1
    linarith

theorem exists_lower (a : C) : ∃ b : ℕ, V.Ge (-(b : ℝ)) a := by
  unfold VF.Ge
  induction hv : V.v a using WithTop.recTopCoe with
  | top => exact ⟨0, le_top⟩
  | coe t =>
    obtain ⟨N, hN⟩ := exists_nat_gt (-t)
    refine ⟨N, ?_⟩
    have : -(N : ℝ) ≤ t := by linarith
    exact_mod_cast this

theorem ge_l_pow (n : ℕ) : V.Ge n ((V.l : C) ^ n) := by
  induction n with
  | zero => simpa using VF.Ge.one (V := V)
  | succ n ih => rw [pow_succ]; push_cast; exact ih.mul VF.ge_l

theorem ge_of_unit_mul {c a : C} {w : ℝ} (hc : V.MM c) (h : V.Ge w ((1 - c) * a)) : V.Ge w a := by
  have h1 : V.v (1 - c) ≤ 0 := by
    by_contra hh
    have : V.MM (1 - c + c) := mm_add (not_le.mp hh) hc
    rw [sub_add_cancel] at this
    exact not_mm_one this
  unfold VF.Ge at *
  rw [V.v.map_mul] at h
  exact h.trans (add_le_of_nonpos_left h1)

variable {κ : Type} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
theorem exists_lower_vec (v : κ → C) : ∃ b : ℕ, ∀ i, V.Ge (-(b : ℝ)) (v i) := by
  choose b hb using fun i => exists_lower (V := V) (v i)
  refine ⟨∑ i, b i, fun i => (hb i).mono ?_⟩
  have : b i ≤ ∑ j, b j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have h2 : (b i : ℝ) ≤ ((∑ j, b j : ℕ) : ℝ) := by exact_mod_cast this
  linarith

omit [DecidableEq κ] in
theorem ge_mulVec {M : Matrix κ κ C} (hM : ∀ i j, V.Ge 0 (M i j)) {v : κ → C} {w : ℝ}
    (hv : ∀ i, V.Ge w (v i)) (i : κ) : V.Ge w (M.mulVec v i) :=
  VF.Ge.sum fun j _ => (hM i j).mul_int (hv j)

theorem ge_pow_mulVec {M : Matrix κ κ C} (hM : ∀ i j, V.Ge 0 (M i j)) {v : κ → C} {w : ℝ}
    (hv : ∀ i, V.Ge w (v i)) (k : ℕ) : ∀ i, V.Ge w ((M ^ k).mulVec v i) := by
  induction k with
  | zero => simpa using hv
  | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec]; exact ge_mulVec hM ih

omit [DecidableEq κ] in
theorem uniform {P : κ → ℕ → Prop} (h : ∀ i, ∃ n0 : ℕ, ∀ n ≥ n0, P i n) :
    ∃ n0 : ℕ, ∀ n ≥ n0, ∀ i, P i n := by
  choose b hb using h
  refine ⟨∑ i, b i, fun n hn i => hb i n (le_trans ?_ hn)⟩
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

end Val

theorem frob_iter {C : Type} [Field C] {V : VF C} {O : Type} [CommRing O] {d : ℕ}
    (em : ZMod d → (O →+* C)) (h0 : ∀ a x, V.Ge 0 (em a x))
    (h1 : ∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) (a : ZMod d) (x : O) (n : ℕ) :
    V.MM (em (a + n) x - em a x ^ (V.l ^ n)) := by
  induction n with
  | zero => simp [VF.MM]
  | succ n ih =>
    have h2 := mm_pow_sub ih (h0 _ _) ((h0 _ _).pow _) V.l
    have h3 := mm_add (h1 (a + n) x) h2
    rw [← pow_mul, ← pow_succ, sub_add_sub_cancel] at h3
    push_cast
    rwa [← add_assoc]

theorem limit_idempotent_range : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (O : Type) [CommRing O] (κ : Type) [Fintype κ] [DecidableEq κ] (L : O →+* Matrix κ κ C), (∀ x i j, V.Ge 0 (L x i j)) → ∀ (d : ℕ) [NeZero d] (em : ZMod d → (O →+* C)), (∀ a x, V.Ge 0 (em a x)) → (∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) → ∀ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) → (∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y) → ∀ E : Matrix κ κ C, (∀ (N : ℕ) (v : κ → C) i, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (E.mulVec v i - (L (ε ^ (V.l ^ n))).mulVec v i)) → ∀ v : κ → C, ∃ w : ZMod d → κ → C, (∀ a x, (L x).mulVec (w a) = em a x • w a) ∧ E.mulVec v = ∑ a, w a := by
  intro C _ _ V O _ κ _ _ L hL d _ em h0 h1 ε hε hP E hE v
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hF : ∀ x : O, ∃ y, ε * (x ^ (V.l ^ d) - x) = (V.l : O) * y := by
    intro x
    apply hP
    intro a
    have := mm_neg (frob_iter em h0 h1 a x d)
    simpa using this
  have hzero : ∃ w : ZMod d → κ → C, (∀ a x, (L x).mulVec (w a) = em a x • w a) ∧
      (0 : κ → C) = ∑ a, w a := ⟨0, by simp, by simp⟩
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (fun x : O => Matrix.toLin' (L x))
    (fun x y _ => by
      show Matrix.toLin' (L x) * Matrix.toLin' (L y) = Matrix.toLin' (L y) * Matrix.toLin' (L x)
      rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
        ← Matrix.toLin'_mul, ← map_mul, ← map_mul, mul_comm])
    (fun x => Module.End.iSup_maxGenEigenspace_eq_top _)
  have hv : v ∈ ⨆ χ : O → C, ⨅ x, Module.End.maxGenEigenspace (Matrix.toLin' (L x)) (χ x) := by
    rw [htop]; trivial
  induction hv using Submodule.iSup_induction' with
  | zero => simpa using hzero
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, hw'⟩ := hx
    obtain ⟨u, hu, hu'⟩ := hy
    refine ⟨w + u, fun a x => ?_, ?_⟩
    · simp [Matrix.mulVec_add, hw, hu]
    · simp [Matrix.mulVec_add, hw', hu', Finset.sum_add_distrib]
  | mem χ v hv =>
    have hgen : ∀ x, ∃ k : ℕ, ((L x - χ x • (1 : Matrix κ κ C)) ^ k).mulVec v = 0 := by
      intro x
      have := (Submodule.mem_iInf _).mp hv x
      rw [Module.End.mem_maxGenEigenspace] at this
      obtain ⟨k, hk⟩ := this
      refine ⟨k, ?_⟩
      rw [← Matrix.toLin'_apply, Matrix.toLin'_pow, map_sub, map_smul, Matrix.toLin'_one]
      exact hk
    by_cases hv0 : v = 0
    · subst hv0; simpa using hzero
    obtain ⟨ψ, hψχ, hψ⟩ := GlobalTheory.T.exists_integral_character_generalizedEigen C V O κ L hL χ v hv0 hgen
    by_cases hw0 : E.mulVec v = 0
    · rw [hw0]; exact hzero
    set w := E.mulVec v with hwdef
    have hEu : ∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ i,
        V.Ge N (w i - (L (ε ^ (V.l ^ n))).mulVec v i) := fun N => uniform (hE N v)
    have hgenw : ∀ x, ∃ k : ℕ, ((L x - ψ x • (1 : Matrix κ κ C)) ^ k).mulVec w = 0 := by
      intro x
      obtain ⟨k, hk⟩ := hgen x
      rw [← hψχ] at hk
      refine ⟨k, funext fun i => eq_zero_of_ge_all (V := V) fun N => ?_⟩
      obtain ⟨n, hn⟩ := hEu N
      have hint : ∀ i j, V.Ge 0 ((L x - ψ x • (1 : Matrix κ κ C)) i j) := by
        intro i j
        rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        refine (hL x i j).sub ((hψ x).mul_int ?_)
        rw [← map_one L]; exact hL 1 i j
      have hc : Commute (L x - ψ x • (1 : Matrix κ κ C)) (L (ε ^ (V.l ^ n))) := by
        refine Commute.sub_left ((Commute.all _ _).map L) ?_
        exact (Commute.one_left _).smul_left _
      have h2 := ge_pow_mulVec hint (v := w - (L (ε ^ (V.l ^ n))).mulVec v) (hn n le_rfl) k i
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec v _ (L _), (hc.pow_left k).eq, ← Matrix.mulVec_mulVec, hk,
        Matrix.mulVec_zero, sub_zero] at h2
      exact h2
    have hfix : ∀ (N : ℕ) i, ∃ n0 : ℕ, ∀ n ≥ n0,
        V.Ge N (w i - (L (ε ^ (V.l ^ n))).mulVec w i) := by
      intro N i
      obtain ⟨n0, hn0⟩ := hEu N
      obtain ⟨b, hb⟩ := exists_lower_vec (V := V) v
      refine ⟨max n0 (N + b), fun n hn => ?_⟩
      have hn1 : n0 ≤ n := le_trans (le_max_left _ _) hn
      have hn2 : N + b ≤ n := le_trans (le_max_right _ _) hn
      obtain ⟨y, hy⟩ := hε
      obtain ⟨z, hz⟩ := dvd_sub_pow_of_dvd_sub (p := V.l) (a := ε * ε) (b := ε) ⟨y, hy⟩ n
      rw [mul_pow] at hz
      set e := ε ^ (V.l ^ n) with he
      have hA := hn0 n hn1 i
      have hB := ge_mulVec (hL e) (v := w - (L e).mulVec v) (hn0 n hn1) i
      have hC : V.Ge N ((L (e * e - e)).mulVec v i) := by
        rw [hz, map_mul, map_pow, map_natCast, ← Nat.cast_pow, ← nsmul_eq_mul,
          ← Nat.cast_smul_eq_nsmul C, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, Nat.cast_pow]
        refine ((ge_l_pow (n + 1)).mul (ge_mulVec (hL z) hb i)).mono ?_
        have : (N : ℝ) + b ≤ n := by exact_mod_cast hn2
        push_cast; linarith
      have h3 := (hA.sub hB).sub hC
      convert h3 using 1
      simp only [map_sub, map_mul, Matrix.mulVec_sub, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
        Pi.sub_apply]
      ring
    have heig := GlobalTheory.T.eigenvector_of_generalized_eigen_unramified C V O κ L hL d hd ε hε hF ψ w hψ hgenw hfix
    have hnot : ¬ V.MM (ψ ε) := by
      intro hm
      apply hw0
      funext i
      refine eq_zero_of_ge_all (V := V) fun N => ?_
      obtain ⟨n, hn⟩ := hfix N i
      have h2 := hn n le_rfl
      rw [heig, Pi.smul_apply, smul_eq_mul, ← one_sub_mul] at h2
      refine ge_of_unit_mul ?_ h2
      obtain ⟨m, hm'⟩ := Nat.exists_eq_succ_of_ne_zero (pow_ne_zero n V.l_prime.ne_zero)
      rw [hm', map_pow, pow_succ']
      exact mm_mul hm ((hψ ε).pow _)
    have hl : ∀ x y : O, ε * x = (V.l : O) * y → V.MM (ψ x) := by
      intro x y hxy
      have h2 : V.MM (ψ ε * ψ x) := by
        rw [← map_mul, hxy, map_mul, map_natCast]
        exact mm_mul mm_l (hψ y)
      exact (mm_or h2).resolve_left hnot
    have hone : V.MM (ψ ε - 1) := by
      obtain ⟨y, hy⟩ := hε
      have := hl (ε - 1) y (by rw [← hy]; ring)
      simpa using this
    obtain ⟨a, ha⟩ := GlobalTheory.T.exists_embedding_congr_integral_character C V O d em h0 h1 ψ hψ fun x hx => by
      obtain ⟨y, hy⟩ := hP x hx
      exact hl x y hy
    have hψa := GlobalTheory.T.ringHom_eq_of_congruent_integral_unramified C V O d hd ε hε hF ψ (em a) hψ (h0 a) hone ha
    refine ⟨Pi.single a w, fun b x => ?_, by simp⟩
    by_cases hb : b = a
    · subst hb; rw [Pi.single_eq_same, heig, hψa]
    · simp [Pi.single_eq_of_ne hb]

end GlobalTheory.IdemRange
