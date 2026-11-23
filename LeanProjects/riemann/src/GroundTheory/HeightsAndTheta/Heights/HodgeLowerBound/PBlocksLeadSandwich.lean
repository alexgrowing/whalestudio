import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsBlocksLeadSandwich
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEventualPolyLine
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPolySandwich
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

namespace BlocksLeadSandwich

def lineRestr {K : Type*} (p : MvPolynomial K ℚ) (a m : K → ℚ) : Polynomial ℚ :=
  MvPolynomial.aeval (fun k => Polynomial.C (m k) + Polynomial.C (a k) * Polynomial.X) p

theorem eval_lineRestr {K : Type*} (p : MvPolynomial K ℚ) (a m : K → ℚ) (t : ℚ) :
    (lineRestr p a m).eval t = MvPolynomial.eval (fun k => m k + a k * t) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [lineRestr]
  | add p q hp hq => simp only [lineRestr, map_add, Polynomial.eval_add] at *; rw [hp, hq]
  | mul_X p k hp =>
    simp only [lineRestr, map_mul, Polynomial.eval_mul] at *
    rw [hp]
    simp

theorem eq_map_of_eval_nat {Q : Polynomial ℚ} {r : Polynomial ℝ}
    (h : ∀ t : ℕ, ((Q.eval (t : ℚ) : ℚ) : ℝ) = r.eval (t : ℝ)) : r = Q.map (algebraMap ℚ ℝ) := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (Nat.cast_injective (R := ℝ)))
  rintro _ ⟨t, rfl⟩
  show _ = _
  have ht : (t : ℝ) = algebraMap ℚ ℝ (t : ℚ) := by simp
  rw [← h t, ht, Polynomial.eval_map, Polynomial.eval₂_at_apply]
  simp

end BlocksLeadSandwich

open BlocksLeadSandwich in

theorem BlocksLeadSandwich.proof (hLine : GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine.Statement)
    (hSand : GroundTheory.Heights₂.Heights.HilbertSamuel.PolySandwich.Statement) : BlocksLeadSandwich.Statement := by
  intro K L _ _ n a₀ f g p p' hp hp' hf hg hsand a ha
  classical
  have haq : ∀ k, (((a k).toNat : ℕ) : ℚ) = (a k : ℚ) := fun k => by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by linarith [ha k])]
  set Q := lineRestr p (fun k => (a k : ℚ)) (fun _ => (a₀ : ℚ)) with hQ
  set Q' := lineRestr p' (fun x => ((Sum.elim a (0 : L → ℤ) x : ℤ) : ℚ)) (fun _ => (a₀ : ℚ)) with hQ'

  have hF : ∀ t : ℕ, (f (fun k => ((t * (a k).toNat + a₀ : ℕ) : ℤ)) : ℚ) = Q.eval (t : ℚ) := by
    intro t
    rw [hf _ (fun k => Nat.le_add_left _ _), hQ, eval_lineRestr]
    refine congrArg (fun x => MvPolynomial.eval x _) (funext fun k => ?_)
    push_cast
    rw [haq]
    ring
  have hG : ∀ t : ℕ, (g (Sum.elim (fun k => ((t * (a k).toNat + a₀ : ℕ) : ℤ)) fun _ => ((a₀ : ℕ) : ℤ)) : ℚ) =
      Q'.eval (t : ℚ) := by
    intro t
    have h1 := hg (Sum.elim (fun k => t * (a k).toNat + a₀) fun _ => a₀)
      (by intro x; cases x <;> simp)
    have h2 : (Sum.elim (fun k => ((t * (a k).toNat + a₀ : ℕ) : ℤ)) fun _ => ((a₀ : ℕ) : ℤ)) =
        fun x => (((Sum.elim (fun k => t * (a k).toNat + a₀) fun _ => a₀ : K ⊕ L → ℕ) x : ℕ) : ℤ) := by
      funext x; cases x <;> rfl
    rw [h2, h1, hQ', eval_lineRestr]
    refine congrArg (fun x => MvPolynomial.eval x _) (funext fun x => ?_)
    cases x with
    | inl k => simp only [Sum.elim_inl]; push_cast; rw [haq]; ring
    | inr l => simp

  obtain ⟨c, hc⟩ := hsand fun _ => a₀
  have hsq : ∀ t : ℕ, Q.eval (t : ℚ) ≤ Q'.eval (t : ℚ) ∧ Q'.eval (t : ℚ) ≤ Q.eval ((t : ℚ) + c) := by
    intro t
    have hδ : ∀ k, c ≤ c * (a k).toNat := fun k => by
      have : 1 ≤ (a k).toNat := by have := ha k; omega
      nlinarith
    obtain ⟨h1, h2⟩ := hc (fun k => t * (a k).toNat + a₀) (fun k => c * (a k).toNat) hδ
    have h3 : (fun k => (((t * (a k).toNat + a₀) + c * (a k).toNat : ℕ) : ℤ)) =
        fun k => (((t + c) * (a k).toNat + a₀ : ℕ) : ℤ) := by
      funext k; push_cast; ring
    rw [h3] at h2
    have e1 := hF t
    have e2 := hG t
    have e3 := hF (t + c)
    push_cast at e3
    rw [← e1, ← e2, ← e3]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

  obtain ⟨r, hrdeg, hrc, hr⟩ := hLine K n f p a₀ a (fun _ => (a₀ : ℤ)) hp hf
  obtain ⟨r', hr'deg, hr'c, hr'⟩ := hLine (K ⊕ L) n g p' a₀ (Sum.elim a 0) (fun _ => (a₀ : ℤ)) hp' hg
  have hrQ : r = Q.map (algebraMap ℚ ℝ) := by
    refine eq_map_of_eval_nat fun t => ?_
    rw [← hr t, hQ, eval_lineRestr]
    refine congrArg (fun x => ((MvPolynomial.eval x _ : ℚ) : ℝ)) (funext fun k => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hr'Q : r' = Q'.map (algebraMap ℚ ℝ) := by
    refine eq_map_of_eval_nat fun t => ?_
    rw [← hr' t, hQ', eval_lineRestr]
    refine congrArg (fun x => ((MvPolynomial.eval x _ : ℚ) : ℝ)) (funext fun x => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hQ'deg : Q'.natDegree ≤ n := by
    rw [hr'Q, Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective] at hr'deg
    exact hr'deg
  obtain ⟨-, hcoeff⟩ := hSand n c Q Q' hQ'deg (Filter.Eventually.of_forall hsq)
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have key : (eventualValue (mixedDiff (fun _ : Fin n => Sum.elim a (0 : L → ℤ)) g) : ℝ) / n.factorial =
      (eventualValue (mixedDiff (fun _ : Fin n => a) f) : ℝ) / n.factorial := by
    rw [← hrc, ← hr'c, hrQ, hr'Q, Polynomial.coeff_map, Polynomial.coeff_map, hcoeff]
  rw [div_left_inj' hfac] at key
  exact_mod_cast key

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
