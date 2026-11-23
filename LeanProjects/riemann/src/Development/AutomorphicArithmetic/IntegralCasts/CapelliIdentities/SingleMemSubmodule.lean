import Mathlib

theorem UpperTheory.Reformulated.B.SingleMemSubmodule.single_mem :
    ∀ {K : Type} [inst : Field K] (d : Fin (3 : ℕ) → K),
    Function.Injective d →
      ∀ (W : Submodule K (Fin (3 : ℕ) → K)),
        (∀ v ∈ W, (Matrix.diagonal d).mulVec v ∈ W) →
          ∀ {v : Fin (3 : ℕ) → K}, v ∈ W → ∀ {i : Fin (3 : ℕ)}, v i ≠ (0 : K) → Pi.single i (1 : K) ∈ W := by
  intro K _ d hd W hW v hv i hi
  have step : ∀ (c : K), ∀ w ∈ W, (fun l => (d l - c) * w l) ∈ W := by
    intro c w hw
    have h := W.sub_mem (hW w hw) (W.smul_mem c hw)
    have e : (fun l => (d l - c) * w l) = (Matrix.diagonal d).mulVec w - c • w := by
      funext l
      simp only [Pi.sub_apply, Pi.smul_apply, Matrix.mulVec_diagonal, smul_eq_mul]
      ring
    rw [e]
    exact h
  have iter : ∀ s : Finset (Fin 3), (fun l => (∏ j ∈ s, (d l - d j)) * v l) ∈ W := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have e : (fun l => (∏ j ∈ (∅ : Finset (Fin 3)), (d l - d j)) * v l) = v := by
        funext l
        simp
      rw [e]
      exact hv
    | insert a s ha ih =>
      have h := step (d a) _ ih
      have e : (fun l => (∏ j ∈ insert a s, (d l - d j)) * v l)
          = fun l => (d l - d a) * ((∏ j ∈ s, (d l - d j)) * v l) := by
        funext l
        rw [Finset.prod_insert ha, mul_assoc]
      rw [e]
      exact h
  have hc : (∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr ?_) hi
    intro j hj
    exact sub_ne_zero.mpr fun h => (Finset.ne_of_mem_erase hj) (hd h).symm
  have h := W.smul_mem ((∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i)⁻¹
    (iter (Finset.univ.erase i))
  have e : (Pi.single i (1 : K) : Fin 3 → K)
      = ((∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i)⁻¹ •
        (fun l => (∏ j ∈ Finset.univ.erase i, (d l - d j)) * v l) := by
    funext l
    rw [Pi.smul_apply, smul_eq_mul]
    by_cases hl : l = i
    · subst hl
      rw [Pi.single_eq_same, inv_mul_cancel₀ hc]
    · have hz : ∏ j ∈ Finset.univ.erase i, (d l - d j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩) (sub_self _)
      rw [Pi.single_eq_of_ne hl, hz, zero_mul, mul_zero]
  rw [e]
  exact h
