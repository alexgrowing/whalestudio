import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellDef

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.MainNotions.S Matrix

section

variable {K : Type} [Field K] {n : ℕ}

def schExt (A : Matrix (Fin n) (Fin n) K) (c r : Fin n → K) (d : K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  fun a b => Fin.lastCases (motive := fun _ => K) (Fin.lastCases (motive := fun _ => K) d (fun j => r j) b)
    (fun i => Fin.lastCases (motive := fun _ => K) (c i) (fun j => A i j) b) a

@[simp] theorem schExt_cc (A : Matrix (Fin n) (Fin n) K) (c r : Fin n → K) (d : K) (i j : Fin n) :
    schExt A c r d i.castSucc j.castSucc = A i j := by simp [schExt]
@[simp] theorem schExt_cl (A : Matrix (Fin n) (Fin n) K) (c r : Fin n → K) (d : K) (i : Fin n) :
    schExt A c r d i.castSucc (Fin.last n) = c i := by simp [schExt]
@[simp] theorem schExt_lc (A : Matrix (Fin n) (Fin n) K) (c r : Fin n → K) (d : K) (j : Fin n) :
    schExt A c r d (Fin.last n) j.castSucc = r j := by simp [schExt]
@[simp] theorem schExt_ll (A : Matrix (Fin n) (Fin n) K) (c r : Fin n → K) (d : K) :
    schExt A c r d (Fin.last n) (Fin.last n) = d := by simp [schExt]

theorem schExt_self (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    M = schExt (M.submatrix Fin.castSucc Fin.castSucc) (fun i => M i.castSucc (Fin.last n))
      (fun j => M (Fin.last n) j.castSucc) (M (Fin.last n) (Fin.last n)) := by
  ext a b
  refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b <;> simp

theorem schExt_mul (A A' : Matrix (Fin n) (Fin n) K) (c r c' r' : Fin n → K) (d d' : K) :
    schExt A c r d * schExt A' c' r' d' =
      schExt (A * A' + vecMulVec c r') (A *ᵥ c' + d' • c) (r ᵥ* A' + d • r') (r ⬝ᵥ c' + d * d') := by
  ext a b
  refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, vecMulVec_apply, mulVec, vecMul, dotProduct, mul_comm]

theorem schExt_lo (L : Matrix (Fin n) (Fin n) K) (hL : IsLoUni L) (l : Fin n → K) : IsLoUni (schExt L 0 l 1) := by
  intro a b
  refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
  · simp
  · refine ⟨fun h => absurd h (not_lt.2 (Fin.le_last _)), fun h => absurd h (Fin.castSucc_lt_last j).ne'⟩
  · rw [schExt_cl]
    exact ⟨fun _ => rfl, fun h => absurd h (Fin.castSucc_lt_last i).ne⟩
  · simp only [schExt_cc]
    exact ⟨fun h => (hL i j).1 (Fin.castSucc_lt_castSucc_iff.1 h), fun h => (hL i j).2 (Fin.castSucc_injective _ h)⟩

theorem schExt_up (U : Matrix (Fin n) (Fin n) K) (hU : IsUpUni U) (u : Fin n → K) : IsUpUni (schExt U u 0 1) := by
  intro a b
  refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
  · simp
  · rw [schExt_lc]
    exact ⟨fun _ => rfl, fun h => absurd h (Fin.castSucc_lt_last j).ne'⟩
  · refine ⟨fun h => absurd h (not_lt.2 (Fin.le_last _)), fun h => absurd h (Fin.castSucc_lt_last i).ne⟩
  · simp only [schExt_cc]
    exact ⟨fun h => (hU i j).1 (Fin.castSucc_lt_castSucc_iff.1 h), fun h => (hU i j).2 (Fin.castSucc_injective _ h)⟩

end

theorem sch_ptEntry_append {K : Type} [Zero K] (δ : K) : ∀ (bs : List (K × ℕ)) (i j : ℕ),
    i ≤ (bs.map Prod.snd).sum → j ≤ (bs.map Prod.snd).sum →
    ptEntry (bs ++ [(δ, 1)]) i j =
      if i < (bs.map Prod.snd).sum ∧ j < (bs.map Prod.snd).sum then ptEntry bs i j
      else if i = (bs.map Prod.snd).sum ∧ j = (bs.map Prod.snd).sum then δ else 0
  | [], i, j, hi, hj => by
    simp only [List.map_nil, List.sum_nil, Nat.le_zero_eq] at hi hj
    subst hi hj
    simp [ptEntry]
  | (t, s) :: bs, i, j, hi, hj => by
    simp only [List.map_cons, List.sum_cons] at hi hj ⊢
    simp only [List.cons_append, ptEntry]
    by_cases h1 : i < s ∧ j < s
    · rw [if_pos h1, if_pos (⟨by omega, by omega⟩ : i < s + (bs.map Prod.snd).sum ∧ j < s + (bs.map Prod.snd).sum), if_pos h1]
    · rw [if_neg h1]
      by_cases h2 : s ≤ i ∧ s ≤ j
      · rw [if_pos h2, sch_ptEntry_append δ bs (i - s) (j - s) (by omega) (by omega)]
        by_cases h3 : i < s + (bs.map Prod.snd).sum ∧ j < s + (bs.map Prod.snd).sum
        · rw [if_pos h3, if_pos (⟨by omega, by omega⟩ : i - s < (bs.map Prod.snd).sum ∧ j - s < (bs.map Prod.snd).sum), if_neg h1, if_pos h2]
        · rw [if_neg h3, if_neg (by omega : ¬ (i - s < (bs.map Prod.snd).sum ∧ j - s < (bs.map Prod.snd).sum))]
          by_cases h4 : i = s + (bs.map Prod.snd).sum ∧ j = s + (bs.map Prod.snd).sum
          · rw [if_pos h4, if_pos (⟨by omega, by omega⟩ : i - s = (bs.map Prod.snd).sum ∧ j - s = (bs.map Prod.snd).sum)]
          · rw [if_neg h4, if_neg (by omega : ¬ (i - s = (bs.map Prod.snd).sum ∧ j - s = (bs.map Prod.snd).sum))]
      · rw [if_neg h2]
        rw [if_neg (by omega : ¬ (i = s + (bs.map Prod.snd).sum ∧ j = s + (bs.map Prod.snd).sum)), if_neg h1, if_neg h2]
        simp

def schSnoc {K : Type} [Zero K] {n : ℕ} (p : Point K n) (δ : K) (hδ : δ ≠ 0) : Point K (n + 1) :=
  ⟨p.1 ++ [(δ, 1)], by
    refine ⟨fun b hb => ?_, by simp [p.2.2]⟩
    rcases List.mem_append.1 hb with h | h
    · exact p.2.1 b h
    · rw [List.mem_singleton] at h
      subst h
      exact ⟨hδ, le_rfl⟩⟩

theorem sch_ptMat_snoc {K : Type} [Field K] {n : ℕ} (p : Point K n) (δ : K) (hδ : δ ≠ 0) :
    ptMat (schSnoc p δ hδ) = schExt (ptMat p) 0 0 δ := by
  have hs : (p.1.map Prod.snd).sum = n := p.2.2
  ext a b
  have key : ∀ i j : ℕ, i ≤ n → j ≤ n → ptEntry (p.1 ++ [(δ, 1)]) i j =
      if i < n ∧ j < n then ptEntry p.1 i j else if i = n ∧ j = n then δ else 0 := by
    intro i j hi hj
    have := sch_ptEntry_append δ p.1 i j (hs.symm ▸ hi) (hs.symm ▸ hj)
    rwa [hs] at this
  have e : ptMat (schSnoc p δ hδ) a b = ptEntry (p.1 ++ [(δ, 1)]) a.val b.val := rfl
  rw [e, key _ _ (Nat.lt_succ_iff.1 a.isLt) (Nat.lt_succ_iff.1 b.isLt)]
  refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
  · simp
  · have := j.isLt
    simp [this.ne]
  · have := i.isLt
    simp [this.ne]
  · have h1 := i.isLt
    have h2 := j.isLt
    simp [h1, h2, ptMat]

theorem cell_schur : SchurComplementCellExtension := by
  intro K _ n M p hcell hdet0 hdet
  obtain ⟨L0, U0, hL, hU, hM0⟩ := hcell
  set M0 := M.submatrix Fin.castSucc Fin.castSucc with hM0def
  set P0 := ptMat p with hP0
  have hLP : IsUnit (L0 * P0).det := by
    rw [isUnit_iff_ne_zero]
    intro h
    apply hdet0
    rw [hM0, det_mul, h, zero_mul]
  have hPU : IsUnit (P0 * U0).det := by
    rw [isUnit_iff_ne_zero]
    intro h
    apply hdet0
    rw [hM0, Matrix.mul_assoc, det_mul, h, mul_zero]
  set c : Fin n → K := fun i => M i.castSucc (Fin.last n) with hc
  set r : Fin n → K := fun j => M (Fin.last n) j.castSucc with hr
  set d : K := M (Fin.last n) (Fin.last n) with hd
  set u : Fin n → K := (L0 * P0)⁻¹ *ᵥ c with hu
  set l : Fin n → K := r ᵥ* (P0 * U0)⁻¹ with hl
  set δ : K := d - (l ᵥ* P0) ⬝ᵥ u with hδdef
  have e1 : (L0 * P0) *ᵥ u = c := by
    rw [hu, mulVec_mulVec, mul_nonsing_inv _ hLP, one_mulVec]
  have e2 : (l ᵥ* P0) ᵥ* U0 = r := by
    rw [hl, vecMul_vecMul, vecMul_vecMul, nonsing_inv_mul _ hPU, vecMul_one]
  have hfac : M = schExt L0 0 l 1 * schExt P0 0 0 δ * schExt U0 u 0 1 := by
    rw [schExt_mul, schExt_mul]
    conv_lhs => rw [schExt_self M]
    congr 1
    · simp [← hM0def, hM0]
    · simp [e1, ← hc]
    · simp [e2, ← hr]
    · simp [hδdef, ← hd]
  have hδ : δ ≠ 0 := by
    intro h0
    apply hdet
    rw [hfac, det_mul, det_mul]
    have : (schExt P0 0 0 δ).det = 0 := by
      apply det_eq_zero_of_row_eq_zero (Fin.last n)
      intro j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [h0]
    rw [this, mul_zero, zero_mul]
  refine ⟨schSnoc p δ hδ, schExt L0 0 l 1, schExt U0 u 0 1, schExt_lo L0 hL l, schExt_up U0 hU u, ?_⟩
  rw [sch_ptMat_snoc]
  exact hfac

end Formalism.MainNotions.BridgeLemma

end
