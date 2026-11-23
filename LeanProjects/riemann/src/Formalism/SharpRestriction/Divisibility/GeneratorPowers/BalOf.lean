import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FormalGroupLinearSecond

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2b

open MvPolynomial Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

theorem bal_of {P : MvPolynomial (Fin 2 × Fin d) S} {m : ℕ} (hm : 2 ≤ m) (B A Ab : Fin d → Fin d → S)
    (h2 : P - 1 ∈ Io S (Fin 2 × Fin d) ^ 2) (h3 : P - 1 - bil B ∈ Io S (Fin 2 × Fin d) ^ 3)
    (aW0 aB1 : Fin d → MvPolynomial (Fin 2 × Fin d) S)
    (hW0 : ∀ i, aW0 i - lin A (0 : Fin 2) i ∈ Io S (Fin 2 × Fin d) ^ 2)
    (hB1 : ∀ i, aB1 i - lin Ab (1 : Fin 2) i ∈ Io S (Fin 2 × Fin d) ^ 2)
    (hbal : ev2 P aW0 (xs S d 1) - ev2 P (xs S d 0) aB1 ∈ Io S (Fin 2 × Fin d) ^ (m + 1)) :
    Matrix.transpose (Matrix.of A) * Matrix.of B = Matrix.of B * Matrix.of Ab := by
  set W := P - 1 with hWdef
  set h := bil B with hhdef
  have hhI : h ∈ Io S (Fin 2 × Fin d) ^ 2 := bil_mem B
  have hh : h.IsHomogeneous 2 := bil_hom B
  have hmj : ∀ {p : MvPolynomial (Fin 2 × Fin d) S}, p ∈ Io S _ ^ (m + 1) → p ∈ Io S _ ^ (2 + 1) :=
    fun hp => Ideal.pow_le_pow_right (by omega) hp
  have hsq : ∀ {p : MvPolynomial (Fin 2 × Fin d) S}, p ∈ Io S _ ^ 2 → p ∈ Io S _ :=
    fun hp => Ideal.pow_le_self two_ne_zero hp
  have hPW : ∀ (u v : Fin d → MvPolynomial (Fin 2 × Fin d) S), ev2 P u v = 1 + ev2 W u v := by
    intro u v; rw [hWdef, eval_pair_sub, eval_pair_one]; ring
  have hTr : ∀ (u v : Fin d → MvPolynomial (Fin 2 × Fin d) S), (∀ i, u i ∈ Io S _) → (∀ i, v i ∈ Io S _) →
      ev2 W u v - ev2 h u v ∈ Io S _ ^ (2 + 1) := by
    intro u v hu hv
    rw [← eval_pair_sub]
    exact aeval_mem_pow _ (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu, hv]) _ h3
  have hRep : ∀ (u v u' v' : Fin d → MvPolynomial (Fin 2 × Fin d) S), (∀ i, u i ∈ Io S _) →
      (∀ i, v i ∈ Io S _) → (∀ i, u' i ∈ Io S _) → (∀ i, v' i ∈ Io S _) → (∀ i, u i - u' i ∈ Io S _ ^ 2) →
      (∀ i, v i - v' i ∈ Io S _ ^ 2) → ev2 h u v - ev2 h u' v' ∈ Io S _ ^ (2 + 1) := by
    intro u v u' v' hu hv hu' hv' huu hvv
    exact aeval_sub_mem_pow _ _ (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu, hv])
      (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu', hv'])
      (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [huu, hvv]) 2 h hhI
  have hx : ∀ (k : Fin 2) (i : Fin d), xs S d k i ∈ Io S (Fin 2 × Fin d) := fun k i => xs_mem k i
  have hl : ∀ (M : Fin d → Fin d → S) (k : Fin 2) (i : Fin d), lin M k i ∈ Io S (Fin 2 × Fin d) :=
    fun M k i => lin_mem M k i
  have haW0 : ∀ i, aW0 i ∈ Io S _ := fun i => by
    have := add_mem (hsq (hW0 i)) (hl A 0 i); simpa using this
  have haB1 : ∀ i, aB1 i ∈ Io S _ := fun i => by
    have := add_mem (hsq (hB1 i)) (hl Ab 1 i); simpa using this
  have hb1 : ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2)) = ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2)) := by
    have k : ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2)) - ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2)) ∈
        Io S _ ^ (2 + 1) := by
      have e : ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2)) - ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2)) =
          (ev2 P aW0 (xs S d 1) - ev2 P (xs S d 0) aB1) -
          (ev2 W aW0 (xs S d 1) - ev2 h aW0 (xs S d 1)) + (ev2 W (xs S d 0) aB1 - ev2 h (xs S d 0) aB1) -
          (ev2 h aW0 (xs S d 1) - ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2))) +
          (ev2 h (xs S d 0) aB1 - ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2))) := by
        rw [hPW, hPW]; ring
      rw [e]
      exact add_mem (sub_mem (add_mem (sub_mem (hmj hbal) (hTr _ _ haW0 (hx 1))) (hTr _ _ (hx 0) haB1))
        (hRep _ _ _ _ haW0 (hx 1) (hl A 0) (hx 1) hW0 (fun i => by simp)))
        (hRep _ _ _ _ (hx 0) haB1 (hx 0) (hl Ab 1) (fun i => by simp) hB1)
    exact sub_eq_zero.1 (eq_zero_of_isHomogeneous
      ((eval_pair_homogeneous hh _ _ (lin_hom A 0) (xs_hom 1)).sub (eval_pair_homogeneous hh _ _ (xs_hom 0) (lin_hom Ab 1))) k)
  ext i0 l0
  have hc := congrArg (coeff (sil i0 l0)) hb1
  rw [hhdef, eval_pair_bilinear, eval_pair_bilinear, coeff_linL, coeff_linR] at hc
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  exact hc

end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2b
