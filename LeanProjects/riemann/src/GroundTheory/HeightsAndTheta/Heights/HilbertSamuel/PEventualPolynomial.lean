import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEventualPolynomial
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Finset fwdDiff

noncomputable section

namespace EventualPolynomial

variable {K : Type} [DecidableEq K]

def listDiff (L : List K) (g : (K → ℕ) → ℚ) : (K → ℕ) → ℚ :=
  L.foldr (fun k h => Δ_[(Pi.single k 1 : K → ℕ)] h) g

theorem listDiff_cons (k : K) (L : List K) (g : (K → ℕ) → ℚ) (t : K → ℕ) :
    listDiff (k :: L) g t = listDiff L g (t + Pi.single k 1) - listDiff L g t := rfl

theorem listDiff_append (L₁ L₂ : List K) (g : (K → ℕ) → ℚ) :
    listDiff (L₁ ++ L₂) g = listDiff L₁ (listDiff L₂ g) := by
  simp [listDiff, List.foldr_append]

theorem listDiff_replicate (j : ℕ) (k : K) (g : (K → ℕ) → ℚ) :
    listDiff (List.replicate j k) g = (Δ_[(Pi.single k 1 : K → ℕ)])^[j] g := by
  induction j with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ, Function.iterate_succ_apply', ← ih]; rfl

theorem listDiff_zero (L : List K) : listDiff L (0 : (K → ℕ) → ℚ) = 0 := by
  induction L with
  | nil => rfl
  | cons k L ih =>
    funext t
    rw [listDiff_cons, ih]
    simp

theorem listDiff_long {n : ℕ} {g : (K → ℕ) → ℚ}
    (hg : ∀ L : List K, L.length = n + 1 → listDiff L g = 0) (L : List K) (hL : n + 1 ≤ L.length) :
    listDiff L g = 0 := by
  rw [← List.take_append_drop (L.length - (n + 1)) L, listDiff_append,
    hg _ (by simp; omega), listDiff_zero]

def binomPoly (c : ℕ) (k : K) (j : ℕ) : MvPolynomial K ℚ :=
  C ((j.factorial : ℚ)⁻¹) * ∏ i ∈ range j, (X k - C ((c + i : ℕ) : ℚ))

omit [DecidableEq K] in
theorem binomPoly_totalDegree (c : ℕ) (k : K) (j : ℕ) : (binomPoly c k j).totalDegree ≤ j := by
  unfold binomPoly
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ range j, (X k - C ((c + i : ℕ) : ℚ) : MvPolynomial K ℚ).totalDegree
        ≤ ∑ _i ∈ range j, 1 :=
          sum_le_sum fun i _ => (totalDegree_sub_C_le _ _).trans (by rw [totalDegree_X])
    _ = j := by simp

omit [DecidableEq K] in
theorem eval_binomPoly (c : ℕ) (k : K) (j : ℕ) (x : K → ℚ) (m : ℕ) (hx : x k = (m : ℚ) + c) :
    eval x (binomPoly c k j) = (m.choose j : ℚ) := by
  unfold binomPoly
  simp only [map_mul, eval_C, map_prod, map_sub, eval_X, hx]
  have : ∏ i ∈ range j, ((m : ℚ) + c - ((c + i : ℕ) : ℚ)) = ∏ i ∈ range j, ((m : ℚ) - i) :=
    prod_congr rfl fun i _ => by push_cast; ring
  rw [this, ← descPochhammer_eval_eq_prod_range, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, ← mul_assoc,
    inv_mul_cancel₀ (by positivity), one_mul]

theorem newton (c : ℕ) (s : Finset K) : ∀ (n : ℕ) (g : (K → ℕ) → ℚ),
    (∀ L : List K, L.length = n + 1 → listDiff L g = 0) →
    ∃ P : MvPolynomial K ℚ, P.totalDegree ≤ n ∧
      (∀ x y : K → ℚ, (∀ i ∈ s, x i = y i) → eval x P = eval y P) ∧
      ∀ t : K → ℕ, (∀ i ∉ s, t i = 0) → g t = eval (fun i => (t i : ℚ) + c) P := by
  induction s using Finset.induction_on with
  | empty =>
    intro n g _
    refine ⟨C (g 0), by rw [totalDegree_C]; exact Nat.zero_le _, fun x y _ => by simp,
      fun t ht => ?_⟩
    have : t = 0 := funext fun i => ht i (Finset.notMem_empty i)
    simp [this]
  | insert k s hk ih =>
    intro n g hg
    have hg' := listDiff_long hg
    have hsub : ∀ j, ∀ L : List K, L.length = n - j + 1 →
        listDiff L ((Δ_[(Pi.single k 1 : K → ℕ)])^[j] g) = 0 := by
      intro j L hL
      rw [← listDiff_replicate, ← listDiff_append]
      exact hg' _ (by simp; omega)
    choose P hPdeg hPloc hPval using fun j => ih (n - j) _ (hsub j)
    have hzero : ∀ j, n + 1 ≤ j → (Δ_[(Pi.single k 1 : K → ℕ)])^[j] g = 0 := fun j hj => by
      rw [← listDiff_replicate]; exact hg' _ (by simp; omega)
    refine ⟨∑ j ∈ range (n + 1), binomPoly c k j * P j, ?_, ?_, ?_⟩
    · refine totalDegree_finsetSum_le fun j hj => ?_
      have := mem_range.mp hj
      refine (totalDegree_mul _ _).trans ?_
      have h1 := binomPoly_totalDegree c k j
      have h2 := hPdeg j
      omega
    · intro x y hxy
      simp only [map_sum, map_mul]
      refine sum_congr rfl fun j _ => ?_
      rw [hPloc j x y fun i hi => hxy i (mem_insert_of_mem hi)]
      congr 1
      unfold binomPoly
      simp [hxy k (mem_insert_self k s)]
    · intro t ht
      set y : K → ℕ := Function.update t k 0 with hy
      have hyt : t = y + t k • (Pi.single k 1 : K → ℕ) := by
        funext i
        by_cases h : i = k
        · subst h; simp [hy]
        · simp [hy, h]
      have hys : ∀ i ∉ s, y i = 0 := by
        intro i hi
        by_cases h : i = k
        · subst h; simp [hy]
        · simp only [hy, Function.update_of_ne h]; exact ht i (by simp [h, hi])
      have hty : ∀ i ∈ s, (t i : ℚ) + c = (y i : ℚ) + c := by
        intro i hi
        have : i ≠ k := fun h => hk (h ▸ hi)
        simp [hy, Function.update_of_ne this]
      have e1 : ∑ j ∈ range (t k + 1), (t k).choose j • (Δ_[(Pi.single k 1 : K → ℕ)])^[j] g y
          = ∑ j ∈ range (n + t k + 1), ((t k).choose j : ℚ) * (Δ_[(Pi.single k 1 : K → ℕ)])^[j] g y := by
        simp only [nsmul_eq_mul]
        refine sum_subset (s₁ := range (t k + 1)) (fun j hj => by rw [mem_range] at hj ⊢; omega) fun j _ hj => ?_
        rw [mem_range, not_lt] at hj
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
      have e2 : eval (fun i => (t i : ℚ) + c) (∑ j ∈ range (n + 1), binomPoly c k j * P j)
          = ∑ j ∈ range (n + t k + 1), ((t k).choose j : ℚ) * (Δ_[(Pi.single k 1 : K → ℕ)])^[j] g y := by
        rw [map_sum]
        refine Eq.trans ?_ (sum_subset (s₁ := range (n + 1)) (fun j hj => by rw [mem_range] at hj ⊢; omega) fun j _ hj => ?_)
        · refine sum_congr rfl fun j _ => ?_
          rw [map_mul, eval_binomPoly c k j _ (t k) rfl, hPval j y hys,
            hPloc j _ (fun i => (y i : ℚ) + c) hty]
        · rw [mem_range, not_lt] at hj
          rw [hzero j hj]
          simp
      calc g t = g (y + t k • (Pi.single k 1 : K → ℕ)) := congrArg g hyt
        _ = ∑ j ∈ range (t k + 1), (t k).choose j • (Δ_[(Pi.single k 1 : K → ℕ)])^[j] g y :=
          shift_eq_sum_fwdDiff_iter _ g (t k) y
        _ = _ := by rw [e1, e2]

theorem listDiff_eq_mixedDiff (f : (K → ℤ) → ℤ) (c : ℕ) (L : List K) (t : K → ℕ) :
    listDiff L (fun t => (f (fun k => (c : ℤ) + t k) : ℚ)) t =
      (((L.map fun k => (Pi.single k 1 : K → ℤ)).foldr diffStep f)
        (fun k => (c : ℤ) + t k + L.count k) : ℚ) := by
  induction L generalizing t with
  | nil => simp [listDiff]
  | cons k L ih =>
    rw [listDiff_cons, ih, ih, List.map_cons, List.foldr_cons, diffStep, Int.cast_sub]
    have a1 : (fun i => (c : ℤ) + (((t + Pi.single k 1 : K → ℕ) i : ℕ) : ℤ) + (L.count i : ℤ)) =
        fun i => (c : ℤ) + t i + ((k :: L).count i : ℤ) := by
      funext i
      by_cases h : i = k
      · subst h; simp; ring
      · simp [h, Ne.symm h]
    have a2 : (fun i => (c : ℤ) + t i + (L.count i : ℤ)) =
        (fun i => (c : ℤ) + t i + ((k :: L).count i : ℤ)) - Pi.single k 1 := by
      funext i
      by_cases h : i = k
      · subst h; simp; ring
      · simp [h, Ne.symm h]
    rw [a1, a2]

end EventualPolynomial

open EventualPolynomial in

theorem EventualPolynomial.proof : EventualPolynomial.Statement := by
  intro K _ _ n f hf
  have hall : ∀ᶠ m in Filter.atTop, ∀ v : Fin (n + 1) → K,
      mixedDiff (fun i => (Pi.single (v i) 1 : K → ℤ)) f m = 0 :=
    Filter.eventually_all.mpr fun v => hf _
  obtain ⟨m₁, hm₁⟩ := Filter.eventually_atTop.mp hall
  set c : ℕ := ∑ k, (m₁ k).toNat with hcdef
  have hc : ∀ k, m₁ k ≤ (c : ℤ) := fun k => by
    have h1 : (m₁ k).toNat ≤ c := single_le_sum (f := fun k => (m₁ k).toNat) (fun _ _ => Nat.zero_le _) (mem_univ k)
    have h2 := Int.self_le_toNat (m₁ k)
    omega
  have hL : ∀ L : List K, L.length = n + 1 →
      listDiff L (fun t => (f (fun k => (c : ℤ) + t k) : ℚ)) = 0 := by
    intro L hlen
    funext t
    rw [listDiff_eq_mixedDiff]
    obtain ⟨v, rfl⟩ : ∃ v : Fin (n + 1) → K, List.ofFn v = L :=
      ⟨fun i => L[i.val]'(by have := i.isLt; omega),
        List.ext_getElem (by simp [hlen]) fun j _ _ => by rw [List.getElem_ofFn]⟩
    have hv := hm₁ (fun k => (c : ℤ) + t k + (List.ofFn v).count k)
      (fun k => by have := hc k; dsimp; omega) v
    have hmap : (List.ofFn v).map (fun k => (Pi.single k 1 : K → ℤ)) =
        List.ofFn (fun i => (Pi.single (v i) 1 : K → ℤ)) := by rw [List.map_ofFn]; rfl
    rw [hmap]
    change ((mixedDiff (fun i => (Pi.single (v i) 1 : K → ℤ)) f _ : ℤ) : ℚ) = 0
    rw [hv]
    simp
  obtain ⟨P, hdeg, -, hval⟩ := newton c univ n _ hL
  refine ⟨P, c, hdeg, fun a ha => ?_⟩
  have h1 : ((f fun k => (c : ℤ) + ((a k - c : ℕ) : ℤ) : ℤ) : ℚ) =
      eval (fun i => ((a i - c : ℕ) : ℚ) + c) P :=
    hval (fun k => a k - c) fun i hi => absurd (mem_univ i) hi
  have e1 : (fun k => (c : ℤ) + ((a k - c : ℕ) : ℤ)) = fun k => (a k : ℤ) :=
    funext fun k => by have := ha k; omega
  have e2 : (fun i => ((a i - c : ℕ) : ℚ) + c) = fun k => (a k : ℚ) :=
    funext fun k => by rw [Nat.cast_sub (ha k)]; ring
  rw [e1, e2] at h1
  exact h1

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
