import Formalism.HermitianCurvature.HermitianCurvatureProofs.PrStarFst
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting

namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd

section QPos

theorem sign_facts (U U' : ℕ → ℝ) (k l : ℕ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (hgap : ∀ i, 1 ≤ i → i ≤ k - 1 →
      U (i + 1) ≤ U i - 1 ∧ U' (i + 1) ≤ U' i - 1 ∧ U (i + 1) ≤ U' i - 1 ∧ U' (i + 1) ≤ U i - 1)
    (y : ℝ) (hy : U l + 2 ≤ -y ∧ -y ≤ U' l - 2) :
    (y + 1 / 2 + U l) * (y + 1 / 2 + U' l) < 0 ∧
      ∀ i, 1 ≤ i → i ≤ k → i ≠ l → 0 < (y + 1 / 2 + U i) * (y + 1 / 2 + U' i) := by
  have aU := Formalism.FourierDecayAlt.P.JCTx5.anti_of U k (fun i h1 h2 => by linarith [(hgap i h1 h2).1])
  have aU' := Formalism.FourierDecayAlt.P.JCTx5.anti_of U' k (fun i h1 h2 => by linarith [(hgap i h1 h2).2.1])
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨mul_neg_of_neg_of_pos (by linarith) (by linarith), fun i hi1 hi2 hil => ?_⟩
  rcases lt_or_gt_of_ne hil with h | h
  · have g := hgap i hi1 (by omega)
    have a1 := aU' (i + 1) l (by omega) (by omega) hlk
    exact mul_pos (by linarith [g.2.2.2]) (by linarith [g.2.1])
  · have g := hgap l hl1 (by omega)
    have a1 := aU (l + 1) i (by omega) (by omega) hi2
    have a2 := aU' (l + 1) i (by omega) (by omega) hi2
    exact mul_pos_of_neg_of_neg (by linarith [g.1]) (by linarith [g.2.2.2])

variable (P : M.Par)

theorem qreal_pos (hOK : P.OK) (l : ℕ) (hl1 : 1 ≤ l) (hlk : l ≤ P.k) (y : ℝ) (hy : I.OnCut P.u P.u' l y) :
    0 < -(P.T * P.T') * ∏ i ∈ Icc 1 P.k, ((y + 1 / 2 + P.u i) * (y + 1 / 2 + P.u' i)) := by
  have hs : (y + 1 / 2 + P.u l) * (y + 1 / 2 + P.u' l) < 0 ∧
      ∀ i, 1 ≤ i → i ≤ P.k → i ≠ l → 0 < (y + 1 / 2 + P.u i) * (y + 1 / 2 + P.u' i) := by
    rcases hy with hy | hy
    · exact sign_facts P.u P.u' P.k l hl1 hlk (Formalism.FourierDecayAlt.P.JCTx5.gap4 P hOK) y hy
    · obtain ⟨h1, h2⟩ := sign_facts P.u' P.u P.k l hl1 hlk
        (fun i h1 h2 => let g := Formalism.FourierDecayAlt.P.JCTx5.gap4 P hOK i h1 h2; ⟨g.2.1, g.1, g.2.2.2, g.2.2.1⟩) y hy
      refine ⟨by linarith [mul_comm (y + 1 / 2 + P.u l) (y + 1 / 2 + P.u' l)], fun i a b c => ?_⟩
      have := h2 i a b c
      linarith [mul_comm (y + 1 / 2 + P.u i) (y + 1 / 2 + P.u' i)]
  have hl : l ∈ Icc 1 P.k := Finset.mem_Icc.2 ⟨hl1, hlk⟩
  rw [← Finset.mul_prod_erase _ _ hl]
  have hrest : 0 < ∏ i ∈ (Icc 1 P.k).erase l, ((y + 1 / 2 + P.u i) * (y + 1 / 2 + P.u' i)) := by
    apply Finset.prod_pos
    intro i hi
    obtain ⟨hil, hi⟩ := Finset.mem_erase.1 hi
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
    exact hs.2 i hi1 hi2 hil
  have hT : 0 < P.T * P.T' := mul_pos hOK.T_pos hOK.T'_pos
  have := mul_neg_of_neg_of_pos hs.1 hrest
  nlinarith

theorem qC_ofReal (y : ℝ) :
    M.qC P (y : ℂ) = ((-(P.T * P.T') * ∏ i ∈ Icc 1 P.k, ((y + 1 / 2 + P.u i) * (y + 1 / 2 + P.u' i)) : ℝ) : ℂ) := by
  unfold M.qC
  push_cast
  ring

theorem qw_factor {S : Type} (q : ℂ → ℂ) (u : List (Letter ℂ S)) (y : ℝ)
    (h : ∀ l ∈ u, ∃ Y : ℝ, l.pt = Y ∧ 2 < |y - Y|) : ∃ c : ℝ, 0 < c ∧ qw q u (y : ℂ) = (c : ℂ) * q y := by
  induction u with
  | nil => exact ⟨1, one_pos, by simp [qw]⟩
  | cons l u ih =>
    obtain ⟨c, hc, hce⟩ := ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    obtain ⟨Y, hY, hd⟩ := h l List.mem_cons_self
    have hne : y - Y ≠ 0 := by intro h0; rw [h0] at hd; norm_num at hd
    by_cases hp : l.plus = true
    · have hD : 0 < (y - Y + 1) / (y - Y) := by
        rcases lt_or_gt_of_ne hne with h' | h'
        · have : y - Y < -2 := by
            rcases abs_cases (y - Y) with ⟨a, _⟩ | ⟨a, _⟩ <;> linarith
          exact div_pos_of_neg_of_neg (by linarith) h'
        · have : 2 < y - Y := by
            rcases abs_cases (y - Y) with ⟨a, _⟩ | ⟨a, _⟩ <;> linarith
          exact div_pos (by linarith) h'
      refine ⟨c * ((y - Y + 1) / (y - Y)), mul_pos hc hD, ?_⟩
      simp only [qw, hp, if_true, hce, hY]
      push_cast
      ring
    · have hp' : l.plus = false := by simpa using hp
      have hD : 0 < (Y - y) / (Y - y - 1) := by
        rcases lt_or_gt_of_ne hne with h' | h'
        · have : y - Y < -2 := by
            rcases abs_cases (y - Y) with ⟨a, _⟩ | ⟨a, _⟩ <;> linarith
          exact div_pos (by linarith) (by linarith)
        · have : 2 < y - Y := by
            rcases abs_cases (y - Y) with ⟨a, _⟩ | ⟨a, _⟩ <;> linarith
          exact div_pos_of_neg_of_neg (by linarith) (by linarith)
      refine ⟨c * ((Y - y) / (Y - y - 1)), mul_pos hc hD, ?_⟩
      simp only [qw, hp', Bool.false_eq_true, if_false, hce, hY]
      push_cast
      ring

theorem plusW_eq (ys : List ℝ) (w : List C.Letter) : KB.plusW ys w = ys.map (fun y => (true, y)) ++ w := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp [KB.plusW, ih]

theorem minusW_eq (ys : List ℝ) (w : List C.Letter) :
    KB.minusW ys w = ys.map (fun y => (false, y + 1)) ++ w := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp [KB.minusW, ih]

theorem cutWord_pairwise {l0 : ℕ} {v : List C.Letter} (h : KB.CutWord P l0 v) :
    v.Pairwise (fun a b => 2 < |a.2 - b.2|) := by
  rw [List.pairwise_iff_get]
  intro i j hij
  exact h.2 i j (ne_of_lt hij)

theorem cutWord_mem {l0 : ℕ} {v : List C.Letter} (h : KB.CutWord P l0 v) {a : C.Letter} (ha : a ∈ v) :
    I.OnCut P.u P.u' l0 a.2 := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 ha
  exact h.1 i

theorem qw_pos (hOK : P.OK) (l0 : ℕ) (hl1 : 1 ≤ l0) (hlk : l0 ≤ P.k) (w : List C.Letter) (ys : List ℝ)
    (h1 : KB.CutWord P l0 (KB.plusW ys w)) (_h2 : KB.CutWord P l0 (KB.minusW ys w)) :
    ∀ y ∈ ys, 0 < (qw (M.qC P) (D.positionted w) (y : ℂ)).re ∧ (qw (M.qC P) (D.positionted w) (y : ℂ)).im = 0 := by
  intro y hy
  have hmem : (true, y) ∈ KB.plusW ys w := by
    rw [plusW_eq]; exact List.mem_append_left _ (List.mem_map.2 ⟨y, hy, rfl⟩)
  have hcut := cutWord_mem P h1 hmem
  have hpw := cutWord_pairwise P h1
  rw [plusW_eq] at hpw
  have hsep := (List.pairwise_append.1 hpw).2.2
  obtain ⟨c, hc, hce⟩ := qw_factor (M.qC P) (D.positionted w) y (by
    intro l hl
    unfold D.positionted at hl
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hl
    exact ⟨(w.get a).2, rfl, hsep _ (List.mem_map.2 ⟨y, hy, rfl⟩) _ (List.get_mem _ _)⟩)
  rw [hce, qC_ofReal]
  have hq := qreal_pos P hOK l0 hl1 hlk y hcut
  constructor
  · rw [← Complex.ofReal_mul, Complex.ofReal_re]; exact mul_pos hc hq
  · rw [← Complex.ofReal_mul, Complex.ofReal_im]

end QPos

end Formalism.FourierDecayAlt.P.PBF

namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd

section Lift

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

theorem sum_ix_succ {M : Type*} [AddCommMonoid M] (f : Ix (Fin (n + 1)) → M) :
    ∑ z, f z = ∑ i : Fin 2, ∑ e : Ix (Fin n), f (Fin.cons i e) := by
  rw [← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_bijective (fun p : Fin 2 × Ix (Fin n) => (Fin.cons p.1 p.2 : Ix (Fin (n + 1)))) ⟨?_, ?_⟩ _ _
    (fun p => rfl)
  · rintro ⟨i, e⟩ ⟨i', e'⟩ h
    have h' := Fin.cons_injective2 h
    simp only at h'
    rw [h'.1, h'.2]
  · intro z
    exact ⟨(z 0, Fin.tail z), Fin.cons_self_tail z⟩

theorem ix_ext_iff (z z' : Ix (Fin (n + 1))) : z = z' ↔ z 0 = z' 0 ∧ Fin.tail z = Fin.tail z' := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, ht⟩
    rw [← Fin.cons_self_tail z, ← Fin.cons_self_tail z', h0, ht]

def liftM (M : SlopeTestRemainingChoices (Fin n) A) : SlopeTestRemainingChoices (Fin (n + 1)) A :=
  Matrix.of fun z z' => if z 0 = z' 0 then M (Fin.tail z) (Fin.tail z') else 0

theorem liftM_apply (M : SlopeTestRemainingChoices (Fin n) A) (z z' : Ix (Fin (n + 1))) :
    liftM M z z' = if z 0 = z' 0 then M (Fin.tail z) (Fin.tail z') else 0 := rfl

theorem liftM_one : liftM (1 : SlopeTestRemainingChoices (Fin n) A) = 1 := by
  ext z z'
  rw [liftM_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h0 : z 0 = z' 0
  · by_cases ht : Fin.tail z = Fin.tail z'
    · rw [if_pos h0, if_pos ht, if_pos ((ix_ext_iff z z').2 ⟨h0, ht⟩)]
    · rw [if_pos h0, if_neg ht, if_neg (fun h => ht ((ix_ext_iff z z').1 h).2)]
  · rw [if_neg h0, if_neg (fun h => h0 ((ix_ext_iff z z').1 h).1)]

theorem liftM_zero : liftM (0 : SlopeTestRemainingChoices (Fin n) A) = 0 := by
  ext z z'; simp [liftM_apply]

theorem liftM_add (M N : SlopeTestRemainingChoices (Fin n) A) : liftM (M + N) = liftM M + liftM N := by
  ext z z'; simp only [liftM_apply, Matrix.add_apply]; split_ifs <;> simp

theorem liftM_mul (M N : SlopeTestRemainingChoices (Fin n) A) : liftM (M * N) = liftM M * liftM N := by
  ext z z''
  rw [Matrix.mul_apply, sum_ix_succ]
  simp only [liftM_apply, Fin.cons_zero, Fin.tail_cons, Matrix.mul_apply, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Fin.sum_univ_two]
  by_cases h0 : z 0 = 0 <;> by_cases h1 : z'' 0 = 0
  · simp [h0, h1]
  · have h1' : z'' 0 = 1 := by omega
    simp [h0, h1']
  · have h0' : z 0 = 1 := by omega
    simp [h0', h1]
  · have h0' : z 0 = 1 := by omega
    have h1' : z'' 0 = 1 := by omega
    simp [h0', h1']

theorem liftM_smul (c : ℂ) (M : SlopeTestRemainingChoices (Fin n) A) : liftM (c • M) = c • liftM M := by
  ext z z'; simp only [liftM_apply, Matrix.smul_apply]; split_ifs <;> simp

def liftRingHomSucc : SlopeTestRemainingChoices (Fin n) A →+* SlopeTestRemainingChoices (Fin (n + 1)) A where
  toFun := liftM
  map_one' := liftM_one
  map_mul' := liftM_mul
  map_zero' := liftM_zero
  map_add' := liftM_add

theorem liftRingHom_apply_eq_liftM (M : SlopeTestRemainingChoices (Fin n) A) : (liftRingHomSucc M : SlopeTestRemainingChoices (Fin (n + 1)) A) = liftM M := rfl

theorem eU_succ (a : Fin n) (i j : Fin 2) : (eU a.succ i j : SlopeTestRemainingChoices (Fin (n + 1)) A) = liftM (eU a i j) := by
  ext x y
  rw [liftM_apply]
  simp only [eU, Matrix.of_apply]
  have key : (x a.succ = i ∧ y a.succ = j ∧ ∀ b, b ≠ a.succ → x b = y b) ↔
      (x 0 = y 0 ∧ (Fin.tail x a = i ∧ Fin.tail y a = j ∧ ∀ b, b ≠ a → Fin.tail x b = Fin.tail y b)) := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h3 0 (Fin.succ_ne_zero a).symm, h1, h2, fun b hb => h3 b.succ (fun h => hb (Fin.succ_injective _ h))⟩
    · rintro ⟨h0, h1, h2, h3⟩
      refine ⟨h1, h2, fun b hb => ?_⟩
      exact Fin.cases (motive := fun b => b ≠ a.succ → x b = y b) (fun _ => h0)
        (fun b' hb' => h3 b' (fun h => hb' (by rw [h]))) b hb
  by_cases h0 : x 0 = y 0
  · rw [if_pos h0]
    by_cases h : Fin.tail x a = i ∧ Fin.tail y a = j ∧ ∀ b, b ≠ a → Fin.tail x b = Fin.tail y b
    · rw [if_pos h, if_pos (key.2 ⟨h0, h⟩)]
    · rw [if_neg h, if_neg (fun h' => h (key.1 h').2)]
  · rw [if_neg h0, if_neg (fun h' => h0 (key.1 h').1)]

theorem io_succ (x : A) : (io x : SlopeTestRemainingChoices (Fin (n + 1)) A) = liftM (io x) := by
  ext z z'
  rw [liftM_apply]
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases h0 : z 0 = z' 0
  · by_cases ht : Fin.tail z = Fin.tail z'
    · rw [if_pos h0, if_pos ht, if_pos ((ix_ext_iff z z').2 ⟨h0, ht⟩)]
    · rw [if_pos h0, if_neg ht, if_neg (fun h => ht ((ix_ext_iff z z').1 h).2)]
  · rw [if_neg h0, if_neg (fun h => h0 ((ix_ext_iff z z').1 h).1)]

theorem map_smul_liftM (c : ℂ) (M : M2 (SlopeTestRemainingChoices (Fin n) A)) : (c • M).map liftM = c • M.map liftM := by
  ext i j; simp [liftM_smul]

theorem map_one_liftM : (1 : M2 (SlopeTestRemainingChoices (Fin n) A)).map liftM = 1 := by
  ext i j; simp only [Matrix.map_apply, Matrix.one_apply]; split_ifs <;> simp [liftM_one, liftM_zero]

theorem map_mul_liftM (M N : M2 (SlopeTestRemainingChoices (Fin n) A)) : (M * N).map liftM = M.map liftM * N.map liftM := by
  have := (RingHom.mapMatrix (liftRingHomSucc (A := A) (n := n)) : M2 (SlopeTestRemainingChoices (Fin n) A) →+* M2 (SlopeTestRemainingChoices (Fin (n + 1)) A)).map_mul M N
  exact this

theorem map_sub_liftM (M N : M2 (SlopeTestRemainingChoices (Fin n) A)) : (M - N).map liftM = M.map liftM - N.map liftM := by
  have := (RingHom.mapMatrix (liftRingHomSucc (A := A) (n := n)) : M2 (SlopeTestRemainingChoices (Fin n) A) →+* M2 (SlopeTestRemainingChoices (Fin (n + 1)) A)).map_sub M N
  exact this

theorem basisP_succ_eq_map (a : Fin n) : (P0 a.succ : M2 (SlopeTestRemainingChoices (Fin (n + 1)) A)) = (P0 a).map liftM := by
  ext i j; simp [P0, eU_succ]

theorem basisQ_succ_eq_map (a : Fin n) : (Q0 a.succ : M2 (SlopeTestRemainingChoices (Fin (n + 1)) A)) = (Q0 a).map liftM := by
  ext i j; simp [Q0, eU_succ]

theorem Rh0_succ (a : Fin n) (D : ℂ) : (Rh0 a.succ D : M2 (SlopeTestRemainingChoices (Fin (n + 1)) A)) = (Rh0 a D).map liftM := by
  rw [Rh0, Rh0, map_smul_liftM, map_sub_liftM, map_smul_liftM, map_one_liftM, basisP_succ_eq_map]

theorem Rht0_succ (a : Fin n) (D : ℂ) : (Rht0 a.succ D : M2 (SlopeTestRemainingChoices (Fin (n + 1)) A)) = (Rht0 a D).map liftM := by
  rw [Rht0, Rht0, map_smul_liftM, map_sub_liftM, map_smul_liftM, map_one_liftM, basisQ_succ_eq_map]

theorem liftZero_succ_eq_map (M : M2 A) : (lift0 M : M2 (SlopeTestRemainingChoices (Fin (n + 1)) A)) = (lift0 M).map liftM := by
  ext i j; simp [lift0, io_succ]

theorem ins_succ (a : Fin n) (M : M2 (SlopeTestRemainingChoices (Fin n) A)) : ins a.succ (M.map liftM) = liftM (ins a M) := by
  simp only [ins]
  rw [← liftRingHom_apply_eq_liftM, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, liftRingHom_apply_eq_liftM, liftRingHom_apply_eq_liftM, eU_succ, Matrix.map_apply]

theorem J_succ : (YangianSpanCharacter.T.J (SlopeTestRemainingChoices (Fin (n + 1)) A)) = (YangianSpanCharacter.T.J (SlopeTestRemainingChoices (Fin n) A)).map liftM := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [YangianSpanCharacter.T.J, ← liftRingHom_apply_eq_liftM]

def upL (l : Letter ℂ (Fin n)) : Letter ℂ (Fin (n + 1)) := ⟨l.plus, l.intersection_update_fsHerm_neg_one.succ, l.pt⟩

theorem TTw_succ (QQ : ℂ → M2 A) (u : List (Letter ℂ (Fin n))) (Y : ℂ) :
    TTw QQ (u.map upL) Y = (TTw QQ u Y).map liftM := by
  induction u with
  | nil => simp [TTw, liftZero_succ_eq_map]
  | cons l u ih =>
    simp only [List.map_cons, TTw, upL]
    split_ifs
    · rw [ih, Rh0_succ, map_mul_liftM]
    · rw [ih, Rht0_succ, map_mul_liftM]

theorem RRw_succ (QQ : ℂ → M2 A) (u : List (Letter ℂ (Fin n))) :
    RRw QQ (u.map upL) = liftM (RRw QQ u) := by
  induction u with
  | nil => simp [RRw, liftM_one]
  | cons l u ih =>
    rw [List.map_cons, RRw, RRw, ih, liftM_mul]
    congr 1
    by_cases hp : l.plus = true
    · have hp' : (upL l).plus = true := hp
      rw [if_pos hp', if_pos hp, TTw_succ]
      exact ins_succ l.intersection_update_fsHerm_neg_one _
    · have hp' : ¬ (upL l).plus = true := hp
      rw [if_neg hp', if_neg hp, TTw_succ, ← Matrix.transpose_map]
      exact ins_succ l.intersection_update_fsHerm_neg_one _

theorem JL_succ (L : List (Letter ℂ (Fin n))) : JL (L.map upL) = (liftM (JL L) : SlopeTestRemainingChoices (Fin (n + 1)) A) := by
  induction L with
  | nil => simp [JL, liftM_one]
  | cons l L ih =>
    show ins (upL l).intersection_update_fsHerm_neg_one _ * JL (L.map upL) = _
    rw [ih, JL, liftM_mul]
    congr 1
    by_cases hp : l.plus = true
    · have hp' : (upL l).plus = true := hp
      rw [if_pos hp', if_pos hp, J_succ]
      exact ins_succ l.intersection_update_fsHerm_neg_one _
    · have hp' : ¬ (upL l).plus = true := hp
      rw [if_neg hp', if_neg hp, J_succ, ← Matrix.transpose_map]
      exact ins_succ l.intersection_update_fsHerm_neg_one _

end Lift

end Formalism.FourierDecayAlt.P.PBF

namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd

section ActLift

variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}

theorem pr_sub_fst (p q : Q.Pr V) : (p - q).1 = p.1 - q.1 := rfl

theorem sub_blockMulVec {S : Type} [Fintype S] [DecidableEq S] (M N : SlopeTestRemainingChoices S (Q.Pr V)) (X : Ix S → V) :
    actP (M - N) X = actP M X - actP N X := by
  funext a; simp only [actP, Matrix.sub_apply, pr_sub_fst, LinearMap.sub_apply, Finset.sum_sub_distrib, Pi.sub_apply]

theorem blockMulVec_liftM (M : SlopeTestRemainingChoices (Fin n) (Q.Pr V)) (X : Ix (Fin (n + 1)) → V) (i : Fin 2) (e : Ix (Fin n)) :
    actP (liftM M) X (Fin.cons i e) = actP M (fun e' => X (Fin.cons i e')) e := by
  have key : ∀ (i' : Fin 2) (e' : Ix (Fin n)), (liftM M (Fin.cons i e) (Fin.cons i' e')).1 (X (Fin.cons i' e')) =
      if i = i' then (M e e').1 (X (Fin.cons i' e')) else 0 := by
    intro i' e'
    rw [liftM_apply, Fin.cons_zero, Fin.cons_zero, Fin.tail_cons, Fin.tail_cons]
    split_ifs <;> rfl
  simp only [actP]
  rw [sum_ix_succ]
  simp only [key]
  rw [Fin.sum_univ_two]
  fin_cases i <;> simp

theorem cons_ne_zero_iff (i0 i' : Fin 2) (e e' : Ix (Fin n)) :
    (∀ b : Fin (n + 1), b ≠ 0 → (Fin.cons i0 e : Ix (Fin (n + 1))) b = (Fin.cons i' e' : Ix (Fin (n + 1))) b) ↔
      e = e' := by
  constructor
  · intro h; funext t; exact h t.succ (Fin.succ_ne_zero t)
  · rintro rfl b hb
    obtain ⟨s, rfl⟩ := Fin.exists_succ_eq.2 hb
    simp only [Fin.cons_succ]

theorem insert_unit_matrix_zero_apply {B : Type} [Ring B] (i j i0 : Fin 2) (e : Ix (Fin n)) (z' : Ix (Fin (n + 1))) :
    (eU (0 : Fin (n + 1)) i j : SlopeTestRemainingChoices (Fin (n + 1)) B) (Fin.cons i0 e) z' =
      if i0 = i ∧ z' = Fin.cons j e then 1 else 0 := by
  simp only [eU, Matrix.of_apply, Fin.cons_zero]
  have : (i0 = i ∧ z' 0 = j ∧ ∀ b, b ≠ 0 → (Fin.cons i0 e : Ix (Fin (n + 1))) b = z' b) ↔
      (i0 = i ∧ z' = Fin.cons j e) := by
    rw [← Fin.cons_self_tail z', cons_ne_zero_iff, Fin.cons_zero]
    constructor
    · rintro ⟨h1, h2, h3⟩; rw [h2, ← h3]; exact ⟨h1, rfl⟩
    · rintro ⟨h1, h2⟩
      have h2' := Fin.cons_injective2 h2
      exact ⟨h1, h2'.1, h2'.2.symm⟩
  simp only [this]

theorem act_insert_unit_matrix_zero (i j i0 : Fin 2) (W : Ix (Fin (n + 1)) → V) (e : Ix (Fin n)) :
    actP (eU (0 : Fin (n + 1)) i j : SlopeTestRemainingChoices (Fin (n + 1)) (Q.Pr V)) W (Fin.cons i0 e) =
      if i0 = i then W (Fin.cons j e) else 0 := by
  simp only [actP, insert_unit_matrix_zero_apply]
  have key : ∀ z' : Ix (Fin (n + 1)), ((if i0 = i ∧ z' = Fin.cons j e then (1 : Q.Pr V) else 0).1) (W z') =
      if z' = Fin.cons j e then (if i0 = i then W z' else 0) else 0 := by
    intro z'
    by_cases h1 : i0 = i <;> by_cases h2 : z' = Fin.cons j e <;> simp [h1, h2] <;> rfl
  simp only [key]
  rw [Finset.sum_eq_single (Fin.cons j e) (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ _) h)]
  simp

theorem insert_zero_symplectic_form {B : Type} [Ring B] :
    ins (0 : Fin (n + 1)) (YangianSpanCharacter.T.J (SlopeTestRemainingChoices (Fin (n + 1)) B)) = eU 0 0 1 - eU 0 1 0 := by
  simp [ins, YangianSpanCharacter.T.J, Fin.sum_univ_two, sub_eq_add_neg]

theorem act_insert_symplectic_zero (W : Ix (Fin (n + 1)) → V) (e : Ix (Fin n)) :
    actP (ins (0 : Fin (n + 1)) (YangianSpanCharacter.T.J (SlopeTestRemainingChoices (Fin (n + 1)) (Q.Pr V)))) W (Fin.cons 0 e) = W (Fin.cons 1 e) := by
  rw [insert_zero_symplectic_form, sub_blockMulVec]
  simp only [Pi.sub_apply, act_insert_unit_matrix_zero]
  simp

theorem act_insert_symplectic_one (W : Ix (Fin (n + 1)) → V) (e : Ix (Fin n)) :
    actP (ins (0 : Fin (n + 1)) (YangianSpanCharacter.T.J (SlopeTestRemainingChoices (Fin (n + 1)) (Q.Pr V)))) W (Fin.cons 1 e) = -W (Fin.cons 0 e) := by
  rw [insert_zero_symplectic_form, sub_blockMulVec]
  simp only [Pi.sub_apply, act_insert_unit_matrix_zero]
  simp

theorem cons_comp_cast {m : ℕ} (h : m + 1 = n + 1) (i : Fin 2) (e : Ix (Fin n)) :
    ((Fin.cons i e : Ix (Fin (n + 1))) ∘ Fin.cast h) =
      (Fin.cons i (e ∘ Fin.cast (Nat.succ_injective h)) : Ix (Fin (m + 1))) := by
  funext t
  refine Fin.cases ?_ (fun s => ?_) t
  · have : Fin.cast h 0 = 0 := Fin.ext rfl
    simp only [Function.comp, this, Fin.cons_zero]
  · have : Fin.cast h s.succ = (Fin.cast (Nat.succ_injective h) s).succ := Fin.ext rfl
    simp only [Function.comp, this, Fin.cons_succ]

theorem pair_step {m : ℕ} (β : V → V → ℂ) (hβ : ∀ v v', β (-v) v' = -β v v') (h : m + 1 = n + 1)
    (M : SlopeTestRemainingChoices (Fin n) (Q.Pr V)) (X : Ix (Fin (n + 1)) → V) (X' : Ix (Fin (m + 1)) → V) :
    ∑ z, β (actP (ins (0 : Fin (n + 1)) (YangianSpanCharacter.T.J (SlopeTestRemainingChoices (Fin (n + 1)) (Q.Pr V))) * liftM M) X z)
        (X' (z ∘ Fin.cast h)) =
      ∑ e, β (actP M (fun e' => X (Fin.cons 1 e')) e)
          ((fun e' => X' (Fin.cons 0 e')) (e ∘ Fin.cast (Nat.succ_injective h))) -
        ∑ e, β (actP M (fun e' => X (Fin.cons 0 e')) e)
          ((fun e' => X' (Fin.cons 1 e')) (e ∘ Fin.cast (Nat.succ_injective h))) := by
  rw [polyAction_mul, sum_ix_succ, Fin.sum_univ_two]
  simp only [act_insert_symplectic_zero, act_insert_symplectic_one, blockMulVec_liftM, cons_comp_cast, hβ, Finset.sum_neg_distrib]
  ring

theorem mat_cons (QQ : ℂ → M2 (Q.Pr V)) (y : ℂ) (L W : List (Letter ℂ (Fin n))) :
    JL ((⟨true, 0, y⟩ : Letter ℂ (Fin (n + 1))) :: L.map upL) * RRw QQ (W.map upL) =
      ins (0 : Fin (n + 1)) (YangianSpanCharacter.T.J (SlopeTestRemainingChoices (Fin (n + 1)) (Q.Pr V))) * liftM (JL L * RRw QQ W) := by
  rw [JL, if_pos rfl, JL_succ, RRw_succ, liftM_mul, mul_assoc]

end ActLift

section Slots

theorem positioned_cons (l : C.Letter) (w : List C.Letter) :
    D.positionted (l :: w) = (⟨l.1, 0, (l.2 : ℂ)⟩ : Letter ℂ (Fin (w.length + 1))) :: (D.positionted w).map upL := by
  simp only [D.positionted, List.ofFn_succ, List.map_ofFn]
  rfl

def Lw (ys : List ℝ) (w : List C.Letter) : List (Letter ℂ (Fin (KB.plusW ys w).length)) :=
  (D.positionted (KB.plusW ys w)).take ys.length

def Ww (ys : List ℝ) (w : List C.Letter) : List (Letter ℂ (Fin (KB.plusW ys w).length)) :=
  (D.positionted (KB.plusW ys w)).drop ys.length

theorem Lw_append_Ww (ys : List ℝ) (w : List C.Letter) : Lw ys w ++ Ww ys w = D.positionted (KB.plusW ys w) :=
  List.take_append_drop _ _

theorem Lw_nil (w : List C.Letter) : Lw [] w = [] := rfl

theorem Ww_nil (w : List C.Letter) : Ww [] w = D.positionted w := rfl

theorem Lw_cons (y : ℝ) (ys : List ℝ) (w : List C.Letter) :
    Lw (y :: ys) w = (⟨true, 0, (y : ℂ)⟩ : Letter ℂ (Fin ((KB.plusW ys w).length + 1))) :: (Lw ys w).map upL := by
  show (D.positionted ((true, y) :: KB.plusW ys w)).take (ys.length + 1) = _
  rw [positioned_cons, List.take_succ_cons, Lw, List.map_take]

theorem Ww_cons (y : ℝ) (ys : List ℝ) (w : List C.Letter) : Ww (y :: ys) w = (Ww ys w).map upL := by
  show (D.positionted ((true, y) :: KB.plusW ys w)).drop (ys.length + 1) = _
  rw [positioned_cons, List.drop_succ_cons, Ww, List.map_drop]

theorem len_pm (ys : List ℝ) (w : List C.Letter) : (KB.minusW ys w).length = (KB.plusW ys w).length := by
  simp [plusW_eq, minusW_eq]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem position_pair (β : V → V → ℂ) (hβ : ∀ v v', β (-v) v' = -β v v') (QQ : ℂ → M2 (Q.Pr V))
    (w : List C.Letter) : ∀ (ys : List ℝ) (X : Ix (Fin (KB.plusW ys w).length) → V)
    (X' : Ix (Fin (KB.minusW ys w).length) → V),
    ∑ z, β (actP (JL (Lw ys w) * RRw QQ (Ww ys w)) X z) (X' (z ∘ Fin.cast (len_pm ys w))) =
      KB.pairJ (fun x x' => ∑ e, β (actP (RRw QQ (D.positionted w)) x e) (x' e)) ys X X'
  | [], X, X' => by
    have hc : ∀ z : Ix (Fin w.length), z ∘ Fin.cast (len_pm [] w) = z :=
      fun z => funext fun t => congrArg z (Fin.ext rfl)
    rw [Lw_nil, Ww_nil, JL, one_mul]
    rfl
  | y :: ys, X, X' => by
    have ih := position_pair β hβ QQ w ys
    have h' : (KB.minusW ys w).length + 1 = (KB.plusW ys w).length + 1 := by rw [len_pm]
    have e1 : (JL (Lw (y :: ys) w) * RRw QQ (Ww (y :: ys) w) : SlopeTestRemainingChoices (Fin ((KB.plusW ys w).length + 1)) (Q.Pr V)) =
        ins (0 : Fin ((KB.plusW ys w).length + 1)) (YangianSpanCharacter.T.J (SlopeTestRemainingChoices (Fin ((KB.plusW ys w).length + 1)) (Q.Pr V))) *
          liftM (JL (Lw ys w) * RRw QQ (Ww ys w)) := by
      rw [Lw_cons, Ww_cons]; exact mat_cons QQ (y : ℂ) _ _
    have step := pair_step (n := (KB.plusW ys w).length) β hβ h' (JL (Lw ys w) * RRw QQ (Ww ys w)) X X'
    rw [← e1] at step
    refine step.trans ?_
    show _ - _ = KB.pairJ _ ys (fun e => X (Fin.cons 1 e)) (fun e => X' (Fin.cons 0 e)) -
      KB.pairJ _ ys (fun e => X (Fin.cons 0 e)) (fun e => X' (Fin.cons 1 e))
    congr 1
    · exact ih (fun e' => X (Fin.cons 1 e')) (fun e' => X' (Fin.cons 0 e'))
    · exact ih (fun e' => X (Fin.cons 0 e')) (fun e' => X' (Fin.cons 1 e'))

end Slots

end Formalism.FourierDecayAlt.P.PBF

namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd

section Positions2

def castL {n m : ℕ} (h : n = m) (l : Letter ℂ (Fin n)) : Letter ℂ (Fin m) := ⟨l.plus, Fin.cast h l.intersection_update_fsHerm_neg_one, l.pt⟩

theorem Lw_plus : ∀ (ys : List ℝ) (w : List C.Letter), ∀ l ∈ Lw ys w, l.plus = true
  | [], w => fun l hl => by simp [Lw_nil] at hl
  | y :: ys, w => by
    intro l hl
    rw [Lw_cons] at hl
    rcases List.mem_cons.1 hl with rfl | hl
    · rfl
    · obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
      exact Lw_plus ys w l' hl'

theorem plusW_getElem (ys : List ℝ) (w : List C.Letter) (i : ℕ) (h : i < (KB.plusW ys w).length) :
    (KB.plusW ys w)[i] = if h' : i < ys.length then (true, ys[i]) else
      w[i - ys.length]'(by simp [plusW_eq] at h; omega) := by
  simp only [plusW_eq, List.getElem_append, List.length_map]
  split_ifs <;> simp

theorem minusW_getElem (ys : List ℝ) (w : List C.Letter) (i : ℕ) (h : i < (KB.minusW ys w).length) :
    (KB.minusW ys w)[i] = if h' : i < ys.length then (false, ys[i] + 1) else
      w[i - ys.length]'(by simp [minusW_eq] at h; omega) := by
  simp only [minusW_eq, List.getElem_append, List.length_map]
  split_ifs <;> simp

theorem positioned_getElem (v : List C.Letter) (i : ℕ) (h : i < (D.positionted v).length) :
    (D.positionted v)[i] = ⟨(v[i]'(by simpa [D.positionted] using h)).1, ⟨i, by simpa [D.positionted] using h⟩,
      ((v[i]'(by simpa [D.positionted] using h)).2 : ℂ)⟩ := by
  simp [D.positionted]

theorem len_plusW (ys : List ℝ) (w : List C.Letter) : (KB.plusW ys w).length = ys.length + w.length := by
  simp [plusW_eq]

theorem Lw_dual (ys : List ℝ) (w : List C.Letter) :
    (Lw ys w).map dl ++ Ww ys w = (D.positionted (KB.minusW ys w)).map (castL (len_pm ys w)) := by
  apply List.ext_getElem
  · simp [Lw, Ww, D.positionted, len_pm]
    omega
  · intro i h1 h2
    have hL : (Lw ys w).length = ys.length := by simp [Lw, D.positionted, len_plusW]
    have hi : i < ys.length + w.length := by simpa [D.positionted, minusW_eq] using h2
    rw [List.getElem_map]
    rw [List.getElem_append]
    split_ifs with hc
    · rw [List.getElem_map]
      simp only [Lw, List.getElem_take, positioned_getElem, plusW_getElem, minusW_getElem, castL]
      have hc' : i < ys.length := by rwa [List.length_map, hL] at hc
      simp only [hc', dif_pos, dl, Fin.cast]
      push_cast
      rfl
    · simp only [Ww, List.getElem_drop, positioned_getElem, plusW_getElem, minusW_getElem, castL]
      have hc' : ¬ i < ys.length := by rwa [List.length_map, hL] at hc
      simp only [hc', dif_neg, not_false_eq_true, List.length_map, hL]
      have e1 : ys.length + (i - ys.length) = i := by omega
      simp only [e1, Fin.cast, hc', dif_neg, not_false_eq_true]

theorem castL_rfl {n : ℕ} (u : List (Letter ℂ (Fin n))) : u.map (castL rfl) = u := by
  conv_rhs => rw [← List.map_id u]
  exact List.map_congr_left fun l _ => rfl

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem blockMulVec_cast (QQ : ℂ → M2 (Q.Pr V)) {n m : ℕ} (h : n = m) (u : List (Letter ℂ (Fin n)))
    (X : Ix (Fin n) → V) :
    actP (RRw QQ (u.map (castL h))) (fun z => X (z ∘ Fin.cast h)) = fun z => actP (RRw QQ u) X (z ∘ Fin.cast h) := by
  subst h
  rw [castL_rfl]
  rfl

theorem qw_map_reindex {S S' : Type} (q : ℂ → ℂ) (f : S → S') (u : List (Letter ℂ S)) (Y : ℂ) :
    qw q (u.map fun l => (⟨l.plus, f l.intersection_update_fsHerm_neg_one, l.pt⟩ : Letter ℂ S')) Y = qw q u Y := by
  induction u with
  | nil => rfl
  | cons l u ih => simp only [List.map_cons, qw, ih]

theorem qw_Ww (q : ℂ → ℂ) (w : List C.Letter) : ∀ (ys : List ℝ) (Y : ℂ), qw q (Ww ys w) Y = qw q (D.positionted w) Y
  | [], Y => rfl
  | y :: ys, Y => by
    rw [Ww_cons]
    exact (qw_map_reindex q Fin.succ (Ww ys w) Y).trans (qw_Ww q w ys Y)

theorem Lw_length (ys : List ℝ) (w : List C.Letter) : (Lw ys w).length = ys.length := by
  simp [Lw, D.positionted, len_plusW]

theorem Lw_getElem (ys : List ℝ) (w : List C.Letter) (i : ℕ) (h : i < (Lw ys w).length) :
    (Lw ys w)[i] = ⟨true, ⟨i, by rw [len_plusW]; rw [Lw_length] at h; omega⟩,
      ((ys[i]'(by rwa [Lw_length] at h) : ℝ) : ℂ)⟩ := by
  have h' : i < ys.length := by rwa [Lw_length] at h
  simp only [Lw, List.getElem_take, positioned_getElem, plusW_getElem, h', dif_pos]

theorem Lw_pairwise (w : List C.Letter) (ys : List ℝ) (h : ys.Pairwise fun y y' => 2 < |y - y'|) :
    (Lw ys w).Pairwise fun l l' => l.pt - l'.pt ≠ 0 ∧ l.pt - l'.pt ≠ 1 ∧ l.pt - l'.pt ≠ -1 := by
  rw [List.pairwise_iff_getElem] at h ⊢
  intro i j hi hj hij
  have hi' : i < ys.length := by rwa [Lw_length] at hi
  have hj' : j < ys.length := by rwa [Lw_length] at hj
  have hy := h i j hi' hj' hij
  rw [Lw_getElem, Lw_getElem]
  have hc : ∀ c : ℝ, |c| ≤ 1 → ((ys[i] : ℝ) : ℂ) - (ys[j] : ℝ) ≠ c := by
    intro c hc he
    have : ys[i] - ys[j] = c := by exact_mod_cast he
    rw [this] at hy; linarith
  exact ⟨fun he => hc 0 (by norm_num) (by simpa using he), fun he => hc 1 (by norm_num) (by simpa using he),
    fun he => hc (-1) (by norm_num) (by simpa using he)⟩

end Positions2

end Formalism.FourierDecayAlt.P.PBF
