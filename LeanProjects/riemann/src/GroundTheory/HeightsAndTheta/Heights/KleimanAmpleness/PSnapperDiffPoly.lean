import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperDiffPolySt
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPolyOfDiffs
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

namespace SnapperDiffPoly

def numPt {t : ℕ} (n : Fin t → ℕ) (c : ℤ) : Fin (t + 1) → ℚ :=
  Fin.snoc (α := fun _ => ℚ) (fun j => (n j : ℚ)) (c : ℚ)

theorem eval_aeval_eq {K : Type} (x : K → ℚ) (σ : K → MvPolynomial K ℚ) (P : MvPolynomial K ℚ) :
    eval x (aeval σ P) = eval (fun k => eval x (σ k)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => rw [map_add, map_add, hp, hr, map_add]
  | mul_X p j hp => simp only [map_mul, hp, aeval_X, eval_X]

theorem numPt_succ {t : ℕ} (n : Fin t → ℕ) (c : ℤ) :
    numPt n (c + 1) = numPt n c + Pi.single (Fin.last t) 1 := by
  funext k
  induction k using Fin.lastCases with
  | last => simp [numPt]
  | cast i => simp [numPt, Fin.castSucc_ne_last]

theorem numPt_update {t : ℕ} (n : Fin t → ℕ) (c : ℤ) (j : Fin t) :
    numPt (Function.update n j (n j + 1)) c = numPt n c + Pi.single j.castSucc 1 := by
  funext k
  induction k using Fin.lastCases with
  | last => simp [numPt, (Fin.castSucc_ne_last j).symm]
  | cast i =>
    by_cases h : i = j
    · subst h; simp [numPt]
    · simp [numPt, h, Function.update_apply]

theorem exists_fwd_antideriv {K : Type} [DecidableEq K] (D : ℕ) (k : K) (q : MvPolynomial K ℚ)
    (hq : q = 0 ∨ q.totalDegree < D) : ∃ P : MvPolynomial K ℚ, P.totalDegree ≤ D ∧
      ∀ x : K → ℚ, eval (x + Pi.single k 1) P - eval x P = eval x q := by
  rcases hq with rfl | hq
  · exact ⟨0, by simp, fun x => by simp⟩
  obtain ⟨P₀, hd, he⟩ := FieldNumbers.PolyOfDiffs.exists_antideriv k q
  refine ⟨aeval (fun i => X i - C ((Pi.single k (1 : ℚ) : K → ℚ) i)) P₀, ?_, fun x => ?_⟩
  · refine (FieldNumbers.PolyOfDiffs.totalDegree_aeval_le _ (fun i => ?_) P₀).trans (by omega)
    refine (totalDegree_sub _ _).trans ?_
    simp [totalDegree_X, totalDegree_C]
  · have h1 : (fun i => eval (x + Pi.single k 1) (X i - C ((Pi.single k (1 : ℚ) : K → ℚ) i))) = x := by
      funext i; simp
    have h2 : (fun i => eval x (X i - C ((Pi.single k (1 : ℚ) : K → ℚ) i))) = x - Pi.single k 1 := by
      funext i; simp
    rw [eval_aeval_eq, eval_aeval_eq, h1, h2, he x]

theorem isNumPolyLT_comp {t D : ℕ} {F G : (Fin t → ℕ) → ℤ → ℚ} (σ : Fin (t + 1) → MvPolynomial (Fin (t + 1)) ℚ)
    (hσ : ∀ i, (σ i).totalDegree ≤ 1) (a : (Fin t → ℕ) → ℤ → (Fin t → ℕ)) (b : (Fin t → ℕ) → ℤ → ℤ)
    (hab : ∀ n c, (fun i => eval (numPt n c) (σ i)) = numPt (a n c) (b n c))
    (hG : ∀ n c, G n c = F (a n c) (b n c)) (hF : IsNumPolyLT t D F) : IsNumPolyLT t D G := by
  obtain ⟨Q, hQ, hE⟩ := hF
  refine ⟨aeval σ Q, ?_, fun n c => ?_⟩
  · rcases hQ with rfl | hQ
    · left; simp
    · exact Or.inr ((FieldNumbers.PolyOfDiffs.totalDegree_aeval_le σ hσ Q).trans_lt hQ)
  · rw [hG, hE]
    change _ = eval (numPt n c) (aeval σ Q)
    rw [eval_aeval_eq, hab]
    rfl

theorem isNumPolyLT_shear {t D : ℕ} (ν : Fin t → ℤ) {F : (Fin t → ℕ) → ℤ → ℚ} (hF : IsNumPolyLT t D F) :
    IsNumPolyLT t D (fun n c => F n (c + ∑ i, ν i * (n i : ℤ))) := by
  refine isNumPolyLT_comp (Fin.snoc (α := fun _ => MvPolynomial (Fin (t + 1)) ℚ) (fun i => X i.castSucc)
    (X (Fin.last t) + ∑ i, C (ν i : ℚ) * X i.castSucc)) (fun k => ?_) (fun n _ => n)
    (fun n c => c + ∑ i, ν i * (n i : ℤ)) (fun n c => ?_) (fun n c => rfl) hF
  · induction k using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      refine (totalDegree_add _ _).trans (max_le (by rw [totalDegree_X]) ?_)
      refine totalDegree_finsetSum_le fun i _ => (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, totalDegree_X]
    | cast i => simp [totalDegree_X]
  · funext k
    induction k using Fin.lastCases with
    | last => simp [numPt]
    | cast i => simp [numPt]

theorem unit_steps {t D : ℕ} (g : (Fin t → ℕ) → ℤ → ℚ)
    (hc : IsNumPolyLT t D (fun n c => g n (c + 1) - g n c))
    (hj : ∀ j, IsNumPolyLT t D (fun n c => g (Function.update n j (n j + 1)) c - g n c)) :
    IsNumPolyLT t (D + 1) g := by
  classical
  obtain ⟨Qc, hQc, hcE⟩ := hc
  choose Q hQ hjE using hj
  obtain ⟨Pc, hPcd, hPc⟩ := exists_fwd_antideriv D (Fin.last t) Qc hQc
  choose P hPd hP using fun j : Fin t => exists_fwd_antideriv D j.castSucc (Q j) (hQ j)

  have hcol : ∀ c : ℤ, g 0 c - g 0 0 = eval (numPt 0 c) Pc - eval (numPt 0 0) Pc := by
    have step : ∀ c : ℤ, g 0 (c + 1) - g 0 c = eval (numPt 0 (c + 1)) Pc - eval (numPt 0 c) Pc := by
      intro c
      have h1 : g 0 (c + 1) - g 0 c = eval (numPt 0 c) Qc := hcE 0 c
      rw [h1, numPt_succ, hPc]
    intro c
    induction c using Int.induction_on with
    | zero => simp
    | succ i ih => have := step i; linarith
    | pred i ih =>
      have := step (-(i : ℤ) - 1)
      rw [sub_add_cancel] at this
      linarith

  have hrow : ∀ (i : Fin t) (v : Fin t → ℕ) (c : ℤ) (m : ℕ),
      g (Function.update v i m) c - g (Function.update v i 0) c =
        eval (numPt (Function.update v i m) c) (P i) - eval (numPt (Function.update v i 0) c) (P i) := by
    intro i v c m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 : g (Function.update (Function.update v i m) i (Function.update v i m i + 1)) c -
          g (Function.update v i m) c = eval (numPt (Function.update v i m) c) (Q i) := hjE i _ c
      have h2 := hP i (numPt (Function.update v i m) c)
      rw [← numPt_update] at h2
      simp only [Function.update_self, Function.update_idem] at h1 h2
      linarith

  let tr : Finset (Fin t) → (Fin t → ℕ) → (Fin t → ℕ) := fun s n i => if i ∈ s then n i else 0
  let σ : Finset (Fin t) → Fin (t + 1) → MvPolynomial (Fin (t + 1)) ℚ := fun s =>
    Fin.snoc (α := fun _ => MvPolynomial (Fin (t + 1)) ℚ) (fun i => if i ∈ s then X i.castSucc else 0)
      (X (Fin.last t))
  have hσd : ∀ s k, (σ s k).totalDegree ≤ 1 := by
    intro s k
    induction k using Fin.lastCases with
    | last => simp [σ, totalDegree_X]
    | cast i => simp only [σ, Fin.snoc_castSucc]; split_ifs <;> simp [totalDegree_X]
  have hσe : ∀ s n c, (fun k => eval (numPt n c) (σ s k)) = numPt (tr s n) c := by
    intro s n c
    funext k
    induction k using Fin.lastCases with
    | last => simp [σ, numPt]
    | cast i => simp only [σ, tr, numPt, Fin.snoc_castSucc]; split_ifs <;> simp
  have key : ∀ s : Finset (Fin t), ∃ Γ : MvPolynomial (Fin (t + 1)) ℚ, Γ.totalDegree ≤ D ∧
      ∀ n c, g (tr s n) c = eval (numPt n c) Γ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨aeval (σ ∅) Pc + C (g 0 0 - eval (numPt 0 0) Pc), ?_, fun n c => ?_⟩
      · refine (totalDegree_add _ _).trans (max_le ?_ (by rw [totalDegree_C]; exact Nat.zero_le _))
        exact (FieldNumbers.PolyOfDiffs.totalDegree_aeval_le _ (hσd ∅) _).trans hPcd
      · have h0 : tr ∅ n = 0 := by funext i; simp [tr]
        rw [map_add, eval_C, eval_aeval_eq, hσe, h0]
        linarith [hcol c]
    | insert i s hi ih =>
      obtain ⟨Γ, hΓd, hΓ⟩ := ih
      refine ⟨Γ + (aeval (σ (insert i s)) (P i) - aeval (σ s) (P i)), ?_, fun n c => ?_⟩
      · refine (totalDegree_add _ _).trans (max_le hΓd ((totalDegree_sub _ _).trans (max_le ?_ ?_)))
        · exact (FieldNumbers.PolyOfDiffs.totalDegree_aeval_le _ (hσd _) _).trans (hPd i)
        · exact (FieldNumbers.PolyOfDiffs.totalDegree_aeval_le _ (hσd _) _).trans (hPd i)
      · have e1 : tr (insert i s) n = Function.update (tr s n) i (n i) := by
          funext k
          by_cases hk : k = i
          · subst hk; simp [tr]
          · simp [tr, hk]
        have e2 : tr s n = Function.update (tr s n) i 0 := by
          funext k
          by_cases hk : k = i
          · subst hk; simp [tr, hi]
          · simp [hk]
        have h := hrow i (tr s n) c (n i)
        rw [← e1, ← e2] at h
        rw [map_add, map_sub, eval_aeval_eq, eval_aeval_eq, hσe, hσe, ← hΓ n c]
        linarith
  obtain ⟨Γ, hΓd, hΓ⟩ := key Finset.univ
  refine ⟨Γ, Or.inr (by omega), fun n c => ?_⟩
  have h := hΓ n c
  have hu : tr Finset.univ n = n := by funext i; simp [tr]
  rw [hu] at h
  exact h

end SnapperDiffPoly

theorem SnapperDiffPoly.proof : SnapperDiffPoly.Statement := by
  intro t D f μ hc hj
  classical
  let L : (Fin t → ℕ) → ℤ := fun n => ∑ i, μ i * (n i : ℤ)
  have hL : ∀ n j, L (Function.update n j (n j + 1)) = L n + μ j := by
    intro n j
    simp only [L]
    have : ∀ i, μ i * ((Function.update n j (n j + 1) i : ℕ) : ℤ) =
        μ i * (n i : ℤ) + if i = j then μ j else 0 := by
      intro i
      by_cases h : i = j
      · subst h; simp; ring
      · simp [h]
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  let g : (Fin t → ℕ) → ℤ → ℚ := fun n c => f n (c + L n)
  have hgc : IsNumPolyLT t D (fun n c => g n (c + 1) - g n c) := by
    obtain ⟨Q, hQ, hE⟩ := SnapperDiffPoly.isNumPolyLT_shear μ hc
    refine ⟨Q, hQ, fun n c => ?_⟩
    rw [← hE n c]
    simp only [g, L]
    rw [add_right_comm]
  have hgj : ∀ j, IsNumPolyLT t D (fun n c => g (Function.update n j (n j + 1)) c - g n c) := by
    intro j
    obtain ⟨Q, hQ, hE⟩ := SnapperDiffPoly.isNumPolyLT_shear μ (hj j)
    refine ⟨Q, hQ, fun n c => ?_⟩
    rw [← hE n c]
    simp only [g]
    rw [hL n j, ← add_assoc]
  obtain ⟨Q, hQ, hE⟩ := SnapperDiffPoly.isNumPolyLT_shear (-μ) (SnapperDiffPoly.unit_steps g hgc hgj)
  refine ⟨Q, hQ, fun n c => ?_⟩
  rw [← hE n c]
  simp only [g, L, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  congr 1
  ring

end

end GroundTheory.Heights₂.Heights.Kleiman
