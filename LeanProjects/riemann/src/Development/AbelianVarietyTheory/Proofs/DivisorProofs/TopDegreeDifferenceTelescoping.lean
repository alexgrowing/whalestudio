import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyRegularityCauchyEstimate
open GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O

theorem Calc.top_add_ar_sub {e : ℕ} (M : Man e) (K : Calc M) (v : K.V) (φ φ' : M.Fun) (hφ : M.Smooth φ)
    (hφ' : M.Smooth φ') :
    K.top (v + K.ar φ) - K.top (v + K.ar φ') = ∑ i ∈ Finset.range (e + 1),
      M.int (fun k : Fin e => K.c1 (if (k : ℕ) < i then v + K.ar φ else v + K.ar φ')) (φ - φ') := by
  set a := v + K.ar φ
  set b := v + K.ar φ'
  let w : ℕ → Fin (e + 1) → K.V := fun i k => if (k : ℕ) < i then a else b
  let g : ℕ → ℝ := fun i => K.num (w i)
  have hs : M.Smooth (φ - φ') := fun σ => GlobalTheory.Mean4O.Cauchy.smooth_sub (hφ σ) (hφ' σ)
  have h0 : g 0 = K.top b := by
    simp only [g, w, Calc.top]; congr 1
  have hN : g (e + 1) = K.top a := by
    simp only [g, w, Calc.top]; congr 1; funext k; simp [k.isLt]
  have hab : a - b = K.ar (φ - φ') := by simp [a, b, map_sub]
  have step : ∀ i ∈ Finset.range (e + 1), g (i + 1) - g i =
      M.int (fun k : Fin e => K.c1 (if (k : ℕ) < i then a else b)) (φ - φ') := by
    intro i hi
    have hi' : i < e + 1 := Finset.mem_range.1 hi
    let j : Fin (e + 1) := ⟨i, hi'⟩
    let p : Fin e → K.V := fun k => if (k : ℕ) < i then a else b
    have hw : ∀ x, Function.update (w i) j x = j.insertNth x p := by
      intro x; funext k
      rcases eq_or_ne k j with rfl | hk
      · simp
      · obtain ⟨m, rfl⟩ := Fin.exists_succAbove_eq hk
        rw [Function.update_of_ne hk, Fin.insertNth_apply_succAbove]
        simp only [w, p]
        rcases Nat.lt_or_ge (m : ℕ) i with hm | hm
        · have : j.succAbove m = m.castSucc := Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def, j, hm])
          rw [this]; simp [hm]
        · have : j.succAbove m = m.succ := Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def, j, hm])
          rw [this]; simp only [Fin.val_succ]; rw [if_neg (by omega), if_neg (by omega)]
    have e1 : w (i + 1) = Function.update (w i) j a := by
      funext k
      rcases eq_or_ne k j with rfl | hk
      · simp [w, j]
      · rw [Function.update_of_ne hk]
        have : (k : ℕ) ≠ i := fun h => hk (Fin.ext h)
        simp only [w]
        rcases lt_or_gt_of_ne this with h | h
        · rw [if_pos (by omega), if_pos h]
        · rw [if_neg (by omega), if_neg (by omega)]
    have e2 : w i = Function.update (w i) j b := by
      symm; rw [Function.update_eq_self_iff]; simp [w, j]
    have : g (i + 1) - g i = K.num (Function.update (w i) j (a - b)) := by
      simp only [g]; rw [e1, MultilinearMap.map_update_sub]; congr 1; rw [← e2]
    rw [this, hab, hw, ← K.symm _ j.cycleRange.symm, Fin.insertNth_comp_cycleRange_symm, K.num_ar _ hs]
  rw [← h0, ← hN, ← Finset.sum_range_sub g (e + 1)]
  exact Finset.sum_congr rfl step

end GlobalTheory.Mean4O
