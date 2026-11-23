import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Classical

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.Xgp.c_algsq.LC

open GlobalTheory.CompanionTheory.Ar.PB.CPts

section Pure

variable {N j : ℕ} {a b ca cb : Fin N} {L : Type} [Field L]

def facM {R : Type} [CommRing R] (j : ℕ) (a : Fin N) (h : Matrix (Fin N) (Fin N) R) (i : Fin N) : R :=
  if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ h (wIdx N j) (wIdx N j) else 1)
  else minorIJ h (omIdx N j) (omIdx N j)

theorem facM_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (h : Matrix (Fin N) (Fin N) R) (i : Fin N) :
    facM j a (h.map f) i = f (facM j a h i) := by
  unfold facM
  split_ifs <;> simp [minorIJ_map]

theorem detFac_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (h : Matrix (Fin N) (Fin N) R) (i : Fin N) :
    detFac j i (h.map f) = f (detFac j i h) := by
  unfold detFac
  split_ifs <;> simp [minorIJ_map]

theorem prod_xi {Ψ : Type} [DecidableEq Ψ] (τ : Ψ) (hb : (b : ℕ) = a + 1) (D : Fin N → L) :
    ∏ i, D i ^ xiCoef τ a (τ, i) = (∏ i : Fin N, if (i : ℕ) + 1 = a then D i else 1) * D b * (D a)⁻¹ ^ 2 := by
  have h : ∀ i, D i ^ xiCoef τ a (τ, i) = (if (i : ℕ) + 1 = a then D i else 1) * (if i = b then D i else 1) *
      if i = a then (D i)⁻¹ ^ 2 else 1 := fun i => by
    have e1 : i = b ↔ (i : ℕ) = a + 1 := by rw [Fin.ext_iff, hb]
    have e2 : i = a ↔ (i : ℕ) = a := Fin.ext_iff
    simp only [xiCoef, if_true, e1, e2]
    split_ifs <;> first | omega | (simp; done) | (simp; rfl)
  simp only [h, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]

theorem prod_xi' {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] (τ : Ψ) (D : Ψ × Fin N → L) :
    ∏ p, D p ^ xiCoef τ a p = ∏ i, D (τ, i) ^ xiCoef τ a (τ, i) := by
  rw [Fintype.prod_prod_type, Finset.prod_eq_single τ (fun τ' _ h => ?_) (by simp)]
  exact Finset.prod_eq_one fun i _ => by simp [xiCoef, h]

theorem prod_prev (D D' : Fin N → L) (c : L) (h : ∀ a' : Fin N, (a' : ℕ) + 1 = a → D a' = D' a' * c)
    (h0 : (a : ℕ) = 0 → c = 1) :
    (∏ i : Fin N, if (i : ℕ) + 1 = a then D i else 1) = (∏ i : Fin N, if (i : ℕ) + 1 = a then D' i else 1) * c := by
  by_cases e : (a : ℕ) = 0
  · rw [h0 e, mul_one]
    exact Finset.prod_congr rfl fun i _ => by rw [if_neg (by omega), if_neg (by omega)]
  · let a' : Fin N := ⟨a - 1, by have := a.2; omega⟩
    have ha' : (a' : ℕ) + 1 = a := by simp only [a']; omega
    have hh : ∀ i : Fin N, (i : ℕ) + 1 = a ↔ i = a' := fun i => by rw [Fin.ext_iff]; omega
    simp only [hh, Finset.prod_ite_eq', Finset.mem_univ, if_true]
    exact h a' ha'

theorem minor_empty' {R : Type} [CommRing R] (h : Matrix (Fin N) (Fin N) R) : minorIJ h ∅ ∅ = 1 := by
  rw [MinorCalc.minorIJ_eq_det h ∅ ∅ 0 rfl rfl]
  exact det_isEmpty

theorem scal_main {Ψ : Type} [DecidableEq Ψ] (τ : Ψ) (hj : j ≤ N) (hb : (b : ℕ) = a + 1)
    (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ)) (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1)
    {T B g U V : Matrix (Fin N) (Fin N) L} (hT : IsBlockDiag j T) (hTd : T.det ≠ 0) (hB : IsBlockDiag j B)
    (hU : IsBlockDiag j U) (hUt : U.BlockTriangular id) (hUd : ∀ c, U c c ≠ 0) (e : T * B = g * U) {x s : L}
    (hx : x * (U ca ca + s * U ca cb) = s * U cb cb)
    (hV : (1 + Matrix.single cb ca x) * V = U * (1 + Matrix.single cb ca s)) (υ : Fin N → L) :
    x * ((∏ c ∈ stepCols N j a, V c c) / ∏ c ∈ stepCols N j a, U c c) *
      ∏ i, (if IsProperStep N j i then (detFac j i T * ∏ c ∈ stepCols N j i, U c c)⁻¹
        else υ i / detFac j i T * facM j a g i) ^ xiCoef τ a (τ, i) =
      s * ((∏ i : Fin N, if (i : ℕ) + 1 = a then (if IsProperStep N j i then 1 else υ i * facM j a B i) else 1) *
        if IsProperStep N j b then 1 else υ b * facM j a B b) := by
  have hbN := b.2
  have hca' := hca
  unfold lastCol at hca'
  have hpa : IsProperStep N j a := ⟨by omega, by omega⟩
  have hcaS : ca ∈ stepCols N j a := by
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs at hca' ⊢ <;> omega
  have hcbS : cb ∉ stepCols N j a := by
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs at hca' ⊢ <;> omega
  have hSb : stepCols N j b = insert cb (stepCols N j a) := by
    ext c
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    split_ifs at hca' ⊢ <;> omega
  have hκ : detFac j a T ≠ 0 := detFac_ne_zero hj a hT hTd
  have hW : minorIJ T (wIdx N j) (wIdx N j) * minorIJ B (wIdx N j) (wIdx N j) =
      minorIJ g (wIdx N j) (wIdx N j) * ∏ c ∈ wIdx N j, U c c := by
    rw [← MinorCalc.minorIJ_mul_of_support T B _ _ (MinorCalc.support_wIdx hB), e,
      MinorCalc.minorIJ_mul_of_support g U _ _ (MinorCalc.support_wIdx hU), MinorCalc.minorIJ_self_of_triangular U hUt]
  have hO : minorIJ T (omIdx N j) (omIdx N j) * minorIJ B (omIdx N j) (omIdx N j) =
      minorIJ g (omIdx N j) (omIdx N j) * ∏ c ∈ omIdx N j, U c c := by
    rw [← MinorCalc.minorIJ_mul_of_support T B _ _ (MinorCalc.support_omIdx hB), e,
      MinorCalc.minorIJ_mul_of_support g U _ _ (MinorCalc.support_omIdx hU), MinorCalc.minorIJ_self_of_triangular U hUt]
  have hne : ∀ S : Finset (Fin N), ∏ c ∈ S, U c c ≠ 0 := fun S => Finset.prod_ne_zero_iff.2 fun c _ => hUd c
  set um := ∏ c ∈ (stepCols N j a).erase ca, U c c with hum
  have hum0 : um ≠ 0 := hne _
  have hUa : ∏ c ∈ stepCols N j a, U c c = U ca ca * um := (Finset.mul_prod_erase _ _ hcaS).symm
  have hUb : ∏ c ∈ stepCols N j b, U c c = U cb cb * (U ca ca * um) := by rw [hSb, Finset.prod_insert hcbS, hUa]
  have hVa : ∏ c ∈ stepCols N j a, V c c = (U ca ca + s * U ca cb) * um := by
    have hne' : ca ≠ cb := fun h => hcbS (h ▸ hcaS)
    have ent : ∀ c, c ≠ cb → V c c = U c c + if c = ca then U c cb * s else 0 := fun c hc => by
      have := congrFun (congrFun hV c) c
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.add_apply, Matrix.add_apply,
        Matrix.single_mul_apply_of_ne _ _ _ _ _ hc, add_zero] at this
      rw [this]
      split_ifs with h
      · subst h; rw [Matrix.mul_single_apply_same]
      · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ h]
    rw [← Finset.mul_prod_erase _ _ hcaS, ent ca hne', if_pos rfl, mul_comm s]
    congr 1
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [ent c (fun h => hcbS (h ▸ Finset.mem_of_mem_erase hc)), if_neg (Finset.ne_of_mem_erase hc), add_zero]
  rw [prod_xi τ hb, prod_prev _ (fun i => if IsProperStep N j i then 1 else υ i * facM j a B i) (detFac j a T * um)⁻¹
    (fun a' ha' => ?_) (fun h0 => ?_)]
  · have hnb : (if IsProperStep N j b then (detFac j b T * ∏ c ∈ stepCols N j b, U c c)⁻¹
        else υ b / detFac j b T * facM j a g b) = (if IsProperStep N j b then 1 else υ b * facM j a B b) *
          (detFac j a T * ∏ c ∈ stepCols N j b, U c c)⁻¹ := by
      split_ifs with hp
      · rw [one_mul]
        congr 2
        obtain ⟨h1, h2⟩ := hp
        unfold detFac
        split_ifs <;> first | rfl | omega
      · have hdb : detFac j b T ≠ 0 := detFac_ne_zero hj b hT hTd
        have hn := hne (stepCols N j b)
        by_cases h1 : (b : ℕ) + 1 = j
        · have hS : stepCols N j b = wIdx N j := by
            ext c
            have := c.2
            simp only [stepCols, wIdx, Finset.mem_filter, Finset.mem_univ, true_and]
            split_ifs <;> omega
          have d1 : detFac j a T = 1 := by
            unfold detFac
            rw [if_neg (by omega), if_neg (by omega), one_mul]
          have d2 : detFac j b T = minorIJ T (wIdx N j) (wIdx N j) := by
            unfold detFac
            rw [if_pos (by omega)]
            split_ifs with h2
            · have : omIdx N j = ∅ := by
                ext c
                simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
                omega
              rw [this, minor_empty', mul_one]
            · rw [mul_one]
          rw [d2] at hdb
          rw [hS] at hn
          simp only [facM, if_pos h1, if_pos (show (a : ℕ) < j by omega), d1, d2, hS]
          field_simp
          linear_combination (-υ b) * hW
        · have h2 : (b : ℕ) + 1 = N := by
            by_contra h2; exact hp ⟨h1, h2⟩
          have hS : stepCols N j b = omIdx N j := by
            ext c
            simp only [stepCols, omIdx, Finset.mem_filter, Finset.mem_univ, true_and]
            split_ifs <;> omega
          have d1 : detFac j a T = minorIJ T (wIdx N j) (wIdx N j) := by
            unfold detFac
            rw [if_pos (by omega), if_neg (by omega), mul_one]
          have d2 : detFac j b T = minorIJ T (wIdx N j) (wIdx N j) * minorIJ T (omIdx N j) (omIdx N j) := by
            unfold detFac
            rw [if_pos (by omega), if_pos h2]
          rw [d2] at hdb
          rw [hS] at hn
          have q1 := left_ne_zero_of_mul hdb
          have q2 := right_ne_zero_of_mul hdb
          simp only [facM, if_neg h1, d1, d2, hS]
          field_simp
          linear_combination (-υ b) * hO
    rw [hnb, if_pos hpa, hUb, hUa, hVa]
    have q1 := hUd ca
    have q2 := hUd cb
    generalize (∏ i : Fin N, if (i : ℕ) + 1 = a then (if IsProperStep N j i then 1 else υ i * facM j a B i) else 1) = P
    generalize (if IsProperStep N j b then 1 else υ b * facM j a B b) = Q
    have hs : s = x * (U ca ca + s * U ca cb) / U cb cb := by rw [hx]; field_simp
    generalize U ca ca + s * U ca cb = w at hs ⊢
    rw [hs]
    field_simp
  · split_ifs with hp
    · rw [one_mul]
      obtain ⟨h1, h2⟩ := hp
      congr 2
      · unfold detFac
        split_ifs <;> first | rfl | omega
      · rw [hum]
        congr 1
        ext c
        simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq, Fin.ext_iff]
        split_ifs at hca' ⊢ <;> omega
    · have h1 : (a' : ℕ) + 1 = j := by
        by_contra h1; exact hp ⟨h1, by omega⟩
      have hE : (stepCols N j a).erase ca = ∅ := by
        ext c
        simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq, Fin.ext_iff,
          Finset.notMem_empty, iff_false]
        split_ifs at hca' ⊢ <;> omega
      have d : detFac j a' T = detFac j a T := by
        unfold detFac
        split_ifs <;> first | rfl | omega
      simp only [facM, if_pos h1, if_neg (show ¬ (a : ℕ) < j by omega), d, hum, hE, Finset.prod_empty, mul_one,
        div_eq_mul_inv]
  · have hE : (stepCols N j a).erase ca = ∅ := by
      ext c
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq, Fin.ext_iff,
        Finset.notMem_empty, iff_false]
      split_ifs at hca' ⊢ <;> omega
    have d : detFac j a T = 1 := by
      unfold detFac
      rw [if_neg (show ¬ (a : ℕ) + 1 = N by omega), mul_one]
      split_ifs with h
      · have : wIdx N j = ∅ := by
          ext c
          have := c.2
          simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          omega
        rw [this, minor_empty']
      · rfl
    rw [d, hum, hE, Finset.prod_empty, mul_one, _root_.inv_one]

end Pure

section Deg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (M : FlagModel y Ψ N j) {L : Type} [Field L]

theorem prod_dy (e : K → L) (p : Ψ × Fin N) :
    ∏ k, e k ^ M.dy p k = (∏ k : NonPluckerBlocks M.blk, e k.1 ^ M.b p k)⁻¹ * (M.blk p).elim 1 e := by
  have h : ∀ k, e k ^ M.dy p k = (if h : ∀ p', M.blk p' ≠ some k then (e k ^ M.b p ⟨k, h⟩)⁻¹ else 1) *
      if M.blk p = some k then e k else 1 := fun k => by
    unfold FlagModel.dy
    split_ifs with h1 h2 h3
    · exact absurd h2 (h1 p)
    · rw [_root_.zpow_neg, mul_one]
    · simp
    · simp
  simp only [h, Finset.prod_mul_distrib]
  congr 1
  · rw [← Finset.prod_inv_distrib, Finset.prod_dite]
    simp only [Finset.prod_const_one, mul_one]
    exact Fintype.prod_equiv (Equiv.subtypeEquivRight fun k => by simp) _ _ fun k => rfl
  · cases M.blk p with
    | none => simp
    | some k₁ => simp

theorem zpow_sum' {σ : Type} (S : Finset σ) {x : L} (hx : x ≠ 0) (n : σ → ℤ) :
    x ^ (∑ p ∈ S, n p) = ∏ p ∈ S, x ^ n p := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hx, ih]

theorem prod_deg {τ : Ψ} {a : Fin N} {k₀ : K} (hk : M.blk (τ, a) = some k₀) (e : Option K → L) (he : ∀ o, e o ≠ 0)
    {dg dh : Option K → ℕ} (hd : ∀ o : Option K, (dg o : ℤ) - dh o = o.elim 1 fun k =>
      -(fun k => ∑ p, xiCoef τ a p * M.dy p k) k - (if M.blk (τ, a) = some k then 1 else 0)) :
    (∏ o, e o ^ dh o) * e none = (∏ o, e o ^ dg o) * e (some k₀) *
      ∏ p, ((∏ k : NonPluckerBlocks M.blk, e (some k.1) ^ M.b p k)⁻¹ * (M.blk p).elim 1 fun k => e (some k)) ^ xiCoef τ a p := by
  simp only [← prod_dy M (fun k => e (some k)), ← Finset.prod_zpow]
  rw [Finset.prod_comm, Fintype.prod_option, Fintype.prod_option]
  have h0 : e none ^ dh none * e none = e none ^ dg none := by
    have : dg none = dh none + 1 := by have := hd none; simp only [Option.elim] at this; omega
    rw [this, pow_succ]
  have h1 : ∀ k, e (some k) ^ dh (some k) = e (some k) ^ dg (some k) * (if k = k₀ then e (some k₀) else 1) *
      ∏ p, (e (some k) ^ M.dy p k) ^ xiCoef τ a p := fun k => by
    have := hd (some k)
    simp only [Option.elim, hk, Option.some.injEq] at this
    simp only [← _root_.zpow_mul, mul_comm (M.dy _ k), ← zpow_sum' _ (he _)]
    rw [← zpow_natCast, ← zpow_natCast]
    split_ifs with h
    · subst h
      rw [if_pos rfl] at this
      rw [← zpow_add_one₀ (he _), ← zpow_add₀ (he _)]
      congr 1; omega
    · rw [if_neg (Ne.symm h)] at this
      rw [mul_one, ← zpow_add₀ (he _)]
      congr 1; omega
  simp only [h1, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true, ← h0]
  ring

end Deg

end PositivityTheory.Xgp.c_algsq.LC
