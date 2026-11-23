import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EulerZetaGammaInvIdentity

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.M Finset

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh

def height (P : M.Par) (ρ : M.Ty P) : ℕ := ∑ i, ((ρ i : Fin _) : ℕ)

theorem sum_ind (P : M.Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    ∑ i : Fin (P.k - 1), (if (i : ℕ) + 1 = l then 1 else 0) = 1 := by
  rw [Finset.mem_Icc] at hl
  rw [Finset.sum_eq_single ⟨l - 1, by omega⟩]
  · rw [if_pos (by simp; omega)]
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    ext
    simp
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem up_height (P : M.Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (ρ ρ' : M.Ty P) (hU : M.Up P l ρ ρ') :
    height P ρ' = height P ρ + 1 := by
  unfold height
  rw [Finset.sum_congr rfl (fun i _ => hU i), Finset.sum_add_distrib, sum_ind P l hl]

theorem pred_exists (P : M.Par) (ρ' : M.Ty P) (h : height P ρ' ≠ 0) :
    ∃ l ∈ Icc 1 (P.k - 1), ∃ ρ, M.Up P l ρ ρ' := by
  obtain ⟨i, hi⟩ : ∃ i, ((ρ' i : Fin _) : ℕ) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply h
    unfold height
    exact Finset.sum_eq_zero fun i _ => hall i
  refine ⟨(i : ℕ) + 1, ?_, fun j => if hj : j = i then ⟨((ρ' j : Fin _) : ℕ) - 1,
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (ρ' j).isLt⟩ else ρ' j, ?_⟩
  · rw [Finset.mem_Icc]
    have := i.isLt
    omega
  · intro j
    by_cases hj : j = i
    · subst hj
      simp
      omega
    · simp only [hj, dif_neg, not_false_eq_true]
      rw [if_neg]
      · simp
      · intro h2
        apply hj
        ext
        omega

theorem phase_exists (P : M.Par) (w : ℕ → M.Ty P → M.Ty P → ℂ)
    (hw1 : ∀ l ∈ Icc 1 (P.k - 1), ∀ ρ ρ', M.Up P l ρ ρ' → ‖w l ρ ρ'‖ = 1)
    (hcoc : ∀ l ∈ Icc 1 (P.k - 1), ∀ j ∈ Icc 1 (P.k - 1), j ≠ l → ∀ ρ ρl ρj ρlj : M.Ty P,
      M.Up P l ρ ρl → M.Up P j ρ ρj → M.Up P j ρl ρlj → M.Up P l ρj ρlj →
        w j ρl ρlj * w l ρ ρl = w l ρj ρlj * w j ρ ρj) :
    ∃ u : M.Ty P → ℂ, (∀ ρ, ‖u ρ‖ = 1) ∧
      ∀ l ∈ Icc 1 (P.k - 1), ∀ ρ ρ', M.Up P l ρ ρ' → u ρ' = w l ρ ρ' * u ρ := by
  classical
  have key : ∀ n : ℕ, ∃ u : M.Ty P → ℂ, (∀ ρ, ‖u ρ‖ = 1) ∧
      ∀ l ∈ Icc 1 (P.k - 1), ∀ ρ ρ', M.Up P l ρ ρ' → height P ρ' ≤ n → u ρ' = w l ρ ρ' * u ρ := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun _ => 1, fun _ => by simp, fun l hl ρ ρ' hU hh => ?_⟩
      rw [up_height P l hl ρ ρ' hU] at hh
      omega
    | succ n ih =>
      obtain ⟨u, hu1, hu⟩ := ih
      let u' : M.Ty P → ℂ := fun ρ' =>
        if hh : height P ρ' = n + 1 then
          (let hp := pred_exists P ρ' (by omega)
           w hp.choose hp.choose_spec.2.choose ρ' * u hp.choose_spec.2.choose)
        else u ρ'
      have hu'1 : ∀ ρ, ‖u' ρ‖ = 1 := by
        intro ρ'
        simp only [u']
        split_ifs with hh
        · have hp := pred_exists P ρ' (by omega)
          rw [norm_mul, hw1 _ (pred_exists P ρ' (by omega)).choose_spec.1 _ _
            (pred_exists P ρ' (by omega)).choose_spec.2.choose_spec, hu1, one_mul]
        · exact hu1 ρ'
      refine ⟨u', hu'1, fun l hl ρ ρ' hU hh => ?_⟩
      have hhρ := up_height P l hl ρ ρ' hU
      have hρ : u' ρ = u ρ := by
        simp only [u']
        rw [dif_neg (by omega)]
      rw [hρ]
      by_cases hn : height P ρ' = n + 1
      · simp only [u']
        rw [dif_pos hn]
        set hp := pred_exists P ρ' (by omega) with hpdef
        set l0 := hp.choose with hl0
        have hl0m : l0 ∈ Icc 1 (P.k - 1) := hp.choose_spec.1
        set ρ0 := hp.choose_spec.2.choose with hρ0
        have hU0 : M.Up P l0 ρ0 ρ' := hp.choose_spec.2.choose_spec
        show w l0 ρ0 ρ' * u ρ0 = w l ρ ρ' * u ρ
        by_cases hll : l0 = l
        · have e : ρ0 = ρ := Formalism.FourierDecayAlt.P.Mx4.up_inj P l ρ' ρ0 ρ (hll ▸ hU0) hU
          rw [e, hll]
        · obtain ⟨σ, hσ1, hσ2⟩ := Formalism.FourierDecayAlt.P.Mx4.up_mixed1 P l0 l (Ne.symm hll) ρ ρ' ρ0 hU hU0

          have h0 := up_height P l0 hl0m ρ0 ρ' hU0
          have e1 : u ρ0 = w l σ ρ0 * u σ := hu l hl σ ρ0 hσ2 (by omega)
          have e2 : u ρ = w l0 σ ρ * u σ := hu l0 hl0m σ ρ hσ1 (by omega)
          have hc' := hcoc l0 hl0m l hl (Ne.symm hll) σ ρ ρ0 ρ' hσ1 hσ2 hU hU0
          rw [e1, e2, ← mul_assoc, ← mul_assoc, hc']
      · have hle : height P ρ' ≤ n := by omega
        simp only [u']
        rw [dif_neg hn]
        exact hu l hl ρ ρ' hU hle
  obtain ⟨u, hu1, hu⟩ := key (Finset.univ.sup (height P))
  exact ⟨u, hu1, fun l hl ρ ρ' hU => hu l hl ρ ρ' hU (Finset.le_sup (Finset.mem_univ ρ'))⟩

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh
