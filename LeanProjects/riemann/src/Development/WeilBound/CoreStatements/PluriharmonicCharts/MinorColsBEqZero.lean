import Mathlib
import Development.WeilBound.CoreStatements.PluriharmonicCharts.MinorUpdateColLin
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Classical

noncomputable section

namespace PositivityTheory.Xgp.W

open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

variable {N j : ℕ}

structure Swp (N j : ℕ) (a b ca cb : Fin N) : Prop where
  hj : j ≤ N
  hb : (b : ℕ) = a + 1
  hab : (b : ℕ) < j ∨ j ≤ (a : ℕ)
  hca : (ca : ℕ) = lastCol N j a
  hcb : (cb : ℕ) = ca + 1

theorem mem_stepCols {i c : Fin N} : c ∈ stepCols N j i ↔
    ((i : ℕ) + 1 ≤ j ∧ N - j ≤ (c : ℕ) ∧ (c : ℕ) < N - j + ((i : ℕ) + 1)) ∨ (j < (i : ℕ) + 1 ∧ (c : ℕ) < (i : ℕ) + 1 - j) := by
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> omega

namespace Swp

variable {a b ca cb : Fin N} (s : Swp N j a b ca cb)
include s

theorem ca_val : ((a : ℕ) + 1 ≤ j ∧ (ca : ℕ) = N - j + a) ∨ (j ≤ a ∧ (ca : ℕ) = a - j) := by
  have := s.hca
  unfold lastCol at this
  split_ifs at this <;> omega

theorem ca_mem : ca ∈ stepCols N j a := by
  have := s.ca_val; rw [mem_stepCols]; omega

theorem le_ca (c : Fin N) (hc : c ∈ stepCols N j a) : c ≤ ca := by
  have := s.ca_val; rw [mem_stepCols] at hc; show (c : ℕ) ≤ ca; omega

theorem lt_cb : ca < cb := by have := s.hcb; show (ca : ℕ) < cb; omega

theorem cb_notMem : cb ∉ stepCols N j a := fun h => absurd (s.le_ca _ h) (not_le.2 s.lt_cb)

theorem same : ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) := by
  have := s.ca_val; have := s.hcb; have := s.hb; have := s.hab; have := b.2; have := s.hj; omega

theorem proper : IsProperStep N j a := by
  have := s.hb; have := s.hab; have := b.2; constructor <;> omega

theorem cols_b : stepCols N j b = insert cb (stepCols N j a) := by
  ext c
  have := s.ca_val; have := s.hcb; have := s.hb; have := s.hab; have := b.2; have := s.hj
  rw [Finset.mem_insert, mem_stepCols, mem_stepCols, Fin.ext_iff]; omega

theorem cols_prev {i : Fin N} (hi : (i : ℕ) + 1 = a) (hp : IsProperStep N j i) :
    stepCols N j i = (stepCols N j a).erase ca := by
  ext c
  have := s.ca_val; have := s.hcb; have := s.hb; have := s.hab; have := b.2; have := s.hj; have := hp.1
  rw [Finset.mem_erase, mem_stepCols, mem_stepCols, Ne, Fin.ext_iff]; omega

theorem cols_first (h0 : (a : ℕ) = 0 ∨ (a : ℕ) = j) : (stepCols N j a).erase ca = ∅ := by
  ext c
  have := s.ca_val; have := s.hcb; have := s.hb; have := s.hab; have := b.2; have := s.hj
  rw [Finset.mem_erase, mem_stepCols, Ne, Fin.ext_iff]
  simp only [Finset.notMem_empty, iff_false]; omega

variable {R : Type} [CommRing R]

theorem minor_colsB (A : Matrix (Fin N) (Fin N) R) (I : Finset (Fin N)) :
    minorIJ A I (colsB N j a ca cb) = minorIJ (A.updateCol ca fun r => A r cb) I (stepCols N j a) :=
  minor_swapCol A I _ s.ca_mem s.le_ca s.lt_cb

theorem block_swap {A : Matrix (Fin N) (Fin N) R} (hA : IsBlockDiag j A) :
    IsBlockDiag j (A.updateCol ca fun r => A r cb) := fun r c h => by
  rw [updateCol_apply]
  split_ifs with e
  · exact hA r cb fun e' => h (by rw [e]; exact e'.trans s.same.symm)
  · exact hA r c h

theorem minor_colsB_eq_zero {A : Matrix (Fin N) (Fin N) R} (hA : IsBlockDiag j A) (I : Finset (Fin N))
    (hI : ¬ IsStepRows N j a I) : minorIJ A I (colsB N j a ca cb) = 0 := by
  rw [s.minor_colsB]
  exact minor_stepCols_eq_zero s.hj _ I (s.block_swap hA) hI

theorem minor_colsB_mul (g : Matrix (Fin N) (Fin N) R) {bb : Matrix (Fin N) (Fin N) R} (hbb : IsBlockDiag j bb)
    (hbt : bb.BlockTriangular id) (I : Finset (Fin N)) :
    minorIJ (g * bb) I (colsB N j a ca cb) = (∏ c ∈ (stepCols N j a).erase ca, bb c c) *
      (bb cb cb * minorIJ g I (colsB N j a ca cb) + bb ca cb * minorIJ g I (stepCols N j a)) := by
  let g' := g.updateCol ca (bb cb cb • (fun r => g r cb) + bb ca cb • fun r => g r ca)
  let b' := bb.updateCol ca fun k => if k < ca then bb k cb else if k = ca then 1 else 0
  have hb' : IsBlockDiag j b' := fun r c h => by
    simp only [b', updateCol_apply]
    split_ifs with e e' e''
    · exact hbb r cb fun e' => h (by rw [e]; exact e'.trans s.same.symm)
    · exact absurd (by rw [e, e'']) h
    · rfl
    · exact hbb r c h
  have hb't : b'.BlockTriangular id := fun r c h => by
    have h' : c < r := h
    simp only [b', updateCol_apply]
    split_ifs with e e' e''
    · exact absurd (e ▸ h') (not_lt.2 e'.le)
    · exact absurd (by rw [e, e'']) h'.ne
    · rfl
    · exact hbt h
  have e1 : minorIJ (g * bb) I (colsB N j a ca cb) = minorIJ (g' * b') I (stepCols N j a) := by
    rw [s.minor_colsB]
    refine minor_congr_cols _ _ fun r c hc => ?_
    rw [updateCol_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply]
    split_ifs with e
    · have h1 : ∀ k, g r k * bb k cb = (if k < ca then g r k * bb k cb else 0) +
          ((if k = cb then g r cb * bb cb cb else 0) + if k = ca then g r ca * bb ca cb else 0) := fun k => by
        have h2 := s.hcb
        rcases lt_trichotomy k ca with l | l | l
        · rw [if_pos l, if_neg (l.trans s.lt_cb).ne, if_neg l.ne]; ring
        · rw [if_neg (l ▸ lt_irrefl _), if_neg (l ▸ s.lt_cb.ne), if_pos l, l]; ring
        · rw [if_neg (not_lt.2 l.le), if_neg l.ne']
          by_cases e : k = cb
          · rw [if_pos e, e]; ring
          · have : cb < k := by
              have h3 : (ca : ℕ) < k := l
              have h4 : (k : ℕ) ≠ cb := fun h => e (Fin.ext h)
              show (cb : ℕ) < k
              omega
            rw [if_neg e, hbt this]; ring
      have h2 : ∀ k, g' r k * b' k c = (if k < ca then g r k * bb k cb else 0) +
          if k = ca then g r cb * bb cb cb + g r ca * bb ca cb else 0 := fun k => by
        simp only [g', b', updateCol_apply, if_pos e]
        rcases lt_trichotomy k ca with l | l | l
        · simp [l, l.ne]
        · simp [l]; ring
        · simp [not_lt.2 l.le, l.ne']
      rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_congr rfl fun k _ => h2 k]
      simp [Finset.sum_add_distrib]
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [g', b', updateCol_apply, if_neg e]
      split_ifs with e'
      · rw [e', hbt (lt_of_le_of_ne (s.le_ca c hc) e), mul_zero, mul_zero]
      · rfl
  rw [e1, (minors_main R N j a s.hj).2.2.1 _ _ I hb' hb't, minor_updateCol_lin _ _ _ s.ca_mem, ← s.minor_colsB,
    updateCol_eq_self, ← Finset.mul_prod_erase _ _ s.ca_mem, mul_comm]
  have h3 : b' ca ca = 1 := by simp [b']
  rw [h3, one_mul]
  congr 1
  exact Finset.prod_congr rfl fun c hc => by simp only [b', updateCol_apply, if_neg (Finset.ne_of_mem_erase hc)]

theorem prod_xi {E : Type} [Field E] {Ψ : Type} [DecidableEq Ψ] (τ : Ψ) (f : Fin N → E) :
    ∏ i, f i ^ xiCoef τ a (τ, i) = (∏ i : Fin N, if (i : ℕ) + 1 = a then f i else 1) * f b * ((f a)⁻¹) ^ 2 := by
  have h : ∀ i, f i ^ xiCoef τ a (τ, i) = (if (i : ℕ) + 1 = a then f i else 1) * (if i = b then f b else 1) *
      if i = a then ((f a)⁻¹) ^ 2 else 1 := fun i => by
    have hb := s.hb
    simp only [xiCoef, if_true, Fin.ext_iff]
    by_cases h1 : (i : ℕ) + 1 = a
    · rw [if_pos h1, if_pos h1, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : (i : ℕ) = a + 1
      · rw [if_pos h2, if_neg (by omega), if_pos (by omega), if_neg (by omega), show i = b from Fin.ext (by omega)]
        simp
      · rw [if_neg h2, if_neg (show ¬ (i : ℕ) = b by omega)]
        by_cases h3 : (i : ℕ) = a
        · rw [if_pos h3, if_pos h3, show i = a from Fin.ext h3]
          simp [_root_.zpow_neg, zpow_ofNat]
        · rw [if_neg h3, if_neg h3]; simp
  rw [Finset.prod_congr rfl fun i _ => h i, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp

end Swp

def facI {E : Type} [Field E] (N j : ℕ) (a : Fin N) (lam : Fin N → E) (g : Matrix (Fin N) (Fin N) E) (i : Fin N) : E :=
  if IsProperStep N j i then 1 else lam i * (if (i : ℕ) + 1 = j then
    (if (a : ℕ) < j then minorIJ g (wIdx N j) (wIdx N j) else 1) else minorIJ g (omIdx N j) (omIdx N j))

def nI {E : Type} [Field E] (N j : ℕ) (lam : Fin N → E) (T bb : Matrix (Fin N) (Fin N) E) (i : Fin N) : E :=
  if IsProperStep N j i then detFac j i T * ∏ c ∈ stepCols N j i, bb c c else lam i * detFac j i T

def muI {R : Type} [CommRing R] (N j : ℕ) (b : Fin N) (H : Matrix (Fin N) (Fin N) R) : R :=
  if IsProperStep N j b then 1 else minorIJ H (stepCols N j b) (stepCols N j b)

theorem minor_empty' {R : Type} [CommRing R] (X : Matrix (Fin N) (Fin N) R) : minorIJ X ∅ ∅ = 1 := by
  rw [minor_self_of_lower _ _ (by simp), Finset.prod_empty]

theorem cols_whole (hj : j ≤ N) {b : Fin N} (hp : ¬ IsProperStep N j b) :
    ((b : ℕ) + 1 = j ∧ stepCols N j b = wIdx N j) ∨ ((b : ℕ) + 1 ≠ j ∧ (b : ℕ) + 1 = N ∧ stepCols N j b = omIdx N j) := by
  by_cases h : (b : ℕ) + 1 = j
  · refine Or.inl ⟨h, ?_⟩
    ext c
    have := c.2
    rw [mem_stepCols]; simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]; omega
  · have h' : (b : ℕ) + 1 = N := by by_contra h'; exact hp ⟨h, h'⟩
    refine Or.inr ⟨h, h', ?_⟩
    ext c
    rw [mem_stepCols]; simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]; omega

theorem muI_unit {R : Type} [CommRing R] (hj : j ≤ N) (b : Fin N) {H H' : Matrix (Fin N) (Fin N) R}
    (hH : IsBlockDiag j H) (e : H' * H = 1) : muI N j b H' * muI N j b H = 1 := by
  unfold muI
  split_ifs with hp
  · exact one_mul 1
  · rcases cols_whole hj hp with ⟨-, h⟩ | ⟨-, -, h⟩
    · rw [h, ← minorIJ_mul_of_support _ _ _ _ (support_wIdx hH), e, CPts.minorIJ_one]
    · rw [h, ← minorIJ_mul_of_support _ _ _ _ (support_omIdx hH), e, CPts.minorIJ_one]

theorem Swp.alg {a b ca cb : Fin N} (s : Swp N j a b ca cb) {E : Type} [Field E] {Ψ : Type} [DecidableEq Ψ] (τ : Ψ)
    (lam : Fin N → E) {T g bb H : Matrix (Fin N) (Fin N) E} (hT : IsBlockDiag j T) (hTd : T.det ≠ 0)
    (hH : IsBlockDiag j H) (hbb : IsBlockDiag j bb) (hbt : bb.BlockTriangular id) (hbd : ∀ c, bb c c ≠ 0)
    (e : T * H = g * bb) :
    (∏ i, facI N j a lam g i ^ xiCoef τ a (τ, i)) * bb cb cb =
      muI N j b H * bb ca ca * ∏ i, nI N j lam T bb i ^ xiCoef τ a (τ, i) := by
  have hj := s.hj
  have hb := s.hb
  have hab := s.hab
  have hbN := b.2
  have hD : detFac j a T ≠ 0 := CPts.detFac_ne_zero hj a hT hTd
  set D := detFac j a T with hDdef
  set P := ∏ c ∈ (stepCols N j a).erase ca, bb c c with hPdef
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun c _ => hbd c
  have hPa : ∏ c ∈ stepCols N j a, bb c c = bb ca ca * P := (Finset.mul_prod_erase _ _ s.ca_mem).symm
  have hPb : ∏ c ∈ stepCols N j b, bb c c = bb cb cb * (bb ca ca * P) := by
    rw [s.cols_b, Finset.prod_insert s.cb_notMem, hPa]
  have hfa : facI N j a lam g a = 1 := if_pos s.proper
  have hna : nI N j lam T bb a = D * (bb ca ca * P) := by rw [nI, if_pos s.proper, hPa]
  have hDW : D = if j ≤ a then minorIJ T (wIdx N j) (wIdx N j) else 1 := by
    rw [hDdef, detFac, if_neg (show ¬ (a : ℕ) + 1 = N by omega), mul_one]
    exact if_congr (by omega) rfl rfl
  have h0 : (∏ i : Fin N, if (i : ℕ) + 1 = a then facI N j a lam g i else 1) * (D * P) =
      ∏ i : Fin N, if (i : ℕ) + 1 = a then nI N j lam T bb i else 1 := by
    by_cases ha : (a : ℕ) = 0
    · rw [Finset.prod_eq_one fun i _ => if_neg (by omega), Finset.prod_eq_one fun i _ => if_neg (by omega), hPdef,
        s.cols_first (Or.inl ha), Finset.prod_empty, hDW]
      split_ifs with h
      · rw [show wIdx N j = ∅ by
          ext c; have := c.2; simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
            iff_false]; omega, minor_empty']
        simp
      · simp
    · let i₀ : Fin N := ⟨a - 1, by omega⟩
      have hi : (i₀ : ℕ) + 1 = a := by simp only [i₀]; omega
      have hs : ∀ f : Fin N → E, (∏ i : Fin N, if (i : ℕ) + 1 = a then f i else 1) = f i₀ := fun f => by
        rw [Finset.prod_eq_single i₀ (fun i _ h => if_neg fun e => h (Fin.ext (by omega))) (by simp), if_pos hi]
      rw [hs, hs, facI, nI]
      by_cases hp : IsProperStep N j i₀
      · have := hp.1
        rw [if_pos hp, if_pos hp, s.cols_prev hi hp, one_mul, hDW, detFac, if_neg (show ¬ (i₀ : ℕ) + 1 = N by omega),
          mul_one, hi]
      · have h1 : (i₀ : ℕ) + 1 = j := by by_contra h; exact hp ⟨h, by omega⟩
        rw [if_neg hp, if_neg hp, if_pos h1, if_neg (by omega), hPdef, s.cols_first (Or.inr (by omega)),
          Finset.prod_empty, hDW, detFac, if_neg (show ¬ (i₀ : ℕ) + 1 = N by omega), hi]
        ring
  have h1 : facI N j a lam g b * (D * (bb cb cb * (bb ca ca * P))) = muI N j b H * nI N j lam T bb b := by
    rw [facI, nI, muI, ← hPb]
    by_cases hp : IsProperStep N j b
    · have := hp.1
      rw [if_pos hp, if_pos hp, if_pos hp, hDW, detFac, if_neg hp.2, mul_one]
      congr 2
      exact if_congr (by omega) rfl rfl
    · rw [if_neg hp, if_neg hp, if_neg hp, ← minorIJ_self_of_triangular bb hbt, hDW, detFac]
      rcases cols_whole hj hp with ⟨h, hc⟩ | ⟨h, h', hc⟩
      · have e1 := congrArg (fun X => minorIJ X (wIdx N j) (wIdx N j)) e
        simp only [minorIJ_mul_of_support _ _ _ _ (support_wIdx hH),
          minorIJ_mul_of_support _ _ _ _ (support_wIdx hbb)] at e1
        have e2 : (if (b : ℕ) + 1 = N then minorIJ T (omIdx N j) (omIdx N j) else 1) = 1 := by
          split_ifs with h'
          · rw [show omIdx N j = ∅ by
              ext c; simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
                iff_false]; omega, minor_empty']
          · rfl
        rw [hc, e2, if_pos h, if_pos (by omega), if_neg (by omega), if_pos (by omega)]
        linear_combination (-lam b) * e1
      · have e1 := congrArg (fun X => minorIJ X (omIdx N j) (omIdx N j)) e
        simp only [minorIJ_mul_of_support _ _ _ _ (support_omIdx hH),
          minorIJ_mul_of_support _ _ _ _ (support_omIdx hbb)] at e1
        rw [hc, if_neg h, if_pos (by omega), if_pos (by omega), if_pos h']
        linear_combination (-lam b * minorIJ T (wIdx N j) (wIdx N j)) * e1
  rw [s.prod_xi, s.prod_xi, hfa, hna, ← h0]
  have h2 := hbd ca
  have h3 := hbd cb
  have h4 : facI N j a lam g b = muI N j b H * nI N j lam T bb b / (D * (bb cb cb * (bb ca ca * P))) :=
    eq_div_of_mul_eq (by positivity) h1
  rw [h4]
  field_simp

theorem prod_xi_pair {E : Type} [Field E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] (τ : Ψ) (a : Fin N)
    (f : Ψ × Fin N → E) : ∏ p, f p ^ xiCoef τ a p = ∏ i, f (τ, i) ^ xiCoef τ a (τ, i) := by
  rw [Fintype.prod_prod_type, Finset.prod_eq_single τ (fun τ' _ h => Finset.prod_eq_one fun i _ => by
    simp [xiCoef, h]) (by simp)]

theorem dual_sum {R : Type} [CommRing R] {κ : Type} [Fintype κ] (i : Fin N) (u : κ → Finset (Fin N) → R)
    (u' : Finset (Fin N) → κ → R)
    (hu : ∀ I I', IsStepRows N j i I → IsStepRows N j i I' → ∑ m, u' I m * u m I' = if I = I' then 1 else 0)
    (w : Finset (Fin N) → R) (hw : ∀ I, ¬ IsStepRows N j i I → w I = 0) (I : Finset (Fin N))
    (hI : IsStepRows N j i I) : ∑ m, u' I m * ∑ I', u m I' * w I' = w I := by
  have e1 : ∑ m, u' I m * ∑ I', u m I' * w I' = ∑ I', (∑ m, u' I m * u m I') * w I' := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  rw [e1, Finset.sum_eq_single I]
  · rw [hu I I hI hI, if_pos rfl, one_mul]
  · intro b _ hb
    by_cases hs : IsStepRows N j i b
    · rw [hu I b hI hs, if_neg (Ne.symm hb), zero_mul]
    · rw [hw b hs, mul_zero]
  · simp

theorem dual_sum' {R : Type} [CommRing R] {κ : Type} [Fintype κ] (i : Fin N) (u : κ → Finset (Fin N) → R)
    (u' : Finset (Fin N) → κ → R)
    (hu : ∀ I I', IsStepRows N j i I → IsStepRows N j i I' → ∑ m, u' I m * u m I' = if I = I' then 1 else 0)
    (H H' : Matrix (Fin N) (Fin N) R) (J J' : Finset (Fin N))
    (hw : ∀ I, ¬ IsStepRows N j i I → minorIJ H I J = 0) :
    ∑ m, (∑ I, (if IsStepRows N j i I then minorIJ H' J' I else 0) * u' I m) * ∑ I', u m I' * minorIJ H I' J =
      minorIJ (H' * H) J' J := by
  rw [minorIJ_mul]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => ?_
  split_ifs with hI
  · simp only [mul_assoc]
    rw [← Finset.mul_sum, dual_sum i u u' hu _ hw I hI]
  · simp [hw I hI]

end PositivityTheory.Xgp.W
