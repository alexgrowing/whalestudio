import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O

theorem symm_multilinear_telescope {e : ℕ} {V : Type} [AddCommGroup V] [Module ℝ V]
    (num : MultilinearMap ℝ (fun _ : Fin (e + 1) => V) ℝ)
    (hs : ∀ (v : Fin (e + 1) → V) (π : Equiv.Perm (Fin (e + 1))), num (v ∘ π) = num v) (x d : V) :
    num (fun _ => x + d) - num (fun _ => x) =
      ∑ i ∈ Finset.range (e + 1), num (Fin.cons d (fun l : Fin e => if (l : ℕ) < i then x + d else x)) := by
  set T : ℕ → ℝ := fun i => num (fun k : Fin (e + 1) => if (k : ℕ) < i then x + d else x) with hT
  have h1 : num (fun _ => x + d) = T (e + 1) := by
    simp only [hT]
    congr 1
    funext k
    rw [if_pos k.2]
  have h0 : num (fun _ => x) = T 0 := by
    simp [hT]
  rw [h1, h0, ← Finset.sum_range_sub]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < e + 1 := Finset.mem_range.1 hi
  have ha : T (i + 1) = num (Fin.cons (x + d) (fun l : Fin e => if (l : ℕ) < i then x + d else x)) := by
    simp only [hT]
    congr 1
    funext k
    refine Fin.cases ?_ (fun l => ?_) k
    · simp
    · simp
  have hf : (Fin.cons x (fun l : Fin e => if (l : ℕ) < i then x + d else x) : Fin (e + 1) → V) =
      fun k : Fin (e + 1) => if 0 < (k : ℕ) ∧ (k : ℕ) ≤ i then x + d else x := by
    funext k
    refine Fin.cases ?_ (fun l => ?_) k
    · simp
    · simp [Nat.succ_le_iff]
  have hb : T i = num (Fin.cons x (fun l : Fin e => if (l : ℕ) < i then x + d else x)) := by
    rw [hf, ← hs _ (Equiv.swap 0 ⟨i, hi'⟩)]
    simp only [hT]
    congr 1
    funext k
    simp only [Function.comp]
    refine if_congr ?_ rfl rfl
    have hk0 : k = 0 ↔ (k : ℕ) = 0 := Fin.ext_iff
    have hki : k = ⟨i, hi'⟩ ↔ (k : ℕ) = i := Fin.ext_iff
    rw [Equiv.swap_apply_def]
    by_cases c0 : k = 0
    · rw [if_pos c0]
      have := hk0.1 c0
      simp only
      omega
    · rw [if_neg c0]
      by_cases ci : k = ⟨i, hi'⟩
      · rw [if_pos ci]
        have := hki.1 ci
        simp only [Fin.val_zero]
        omega
      · rw [if_neg ci]
        have h2 := mt hk0.2 c0
        have h3 := mt hki.2 ci
        omega
  rw [ha, hb, MultilinearMap.cons_add]
  ring

theorem top_add_ar_sub : ∀ (e : ℕ) (M : Man e) (K : Calc M) (v : K.V) (u : M.Fun), M.Smooth u →
    K.top (v + K.ar u) - K.top v = ∑ i ∈ Finset.range (e + 1),
      M.int (fun l : Fin e => if (l : ℕ) < i then K.c1 (v + K.ar u) else K.c1 v) u := by
  intro e M K v u hu
  unfold Calc.top
  rw [symm_multilinear_telescope K.num K.symm v (K.ar u)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [K.num_ar u hu]
  congr 1
  funext l
  exact apply_ite _ _ _ _

end GlobalTheory.Mean4O
