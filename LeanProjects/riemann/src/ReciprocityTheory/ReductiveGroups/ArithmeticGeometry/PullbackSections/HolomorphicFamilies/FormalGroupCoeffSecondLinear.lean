import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HStable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.EigenLift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ActLin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.DofComm

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA

section Lin

variable {R : Type} [CommRing R] {d : ℕ}

open Formalism.FG.SolveVAux in

theorem coeff_lin_ev {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS R m d)
    (q : Fin n × Fin d) :
    coeff (Finsupp.single q 1) (ev a f) =
      ∑ p : Fin m × Fin d, coeff (Finsupp.single p 1) f * coeff (Finsupp.single q 1) (a p.1 p.2) := by
  classical
  unfold ev
  have hs : HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2
  have hlow : ∀ p : Fin m × Fin d, Low 1 (a p.1 p.2) := fun p => (low_one_iff _).2 (ha p.1 p.2)
  rw [coeff_subst hs, finsum_eq_sum_of_support_subset _
    (s := Finset.univ.image (fun p : Fin m × Fin d => Finsupp.single p 1))]
  · rw [Finset.sum_image (fun p _ q _ h => Finsupp.single_left_injective one_ne_zero h)]
    refine Finset.sum_congr rfl fun p _ => ?_
    dsimp only
    rw [Finsupp.prod_single_index (h := fun (s : Fin m × Fin d) (e : ℕ) => a s.1 s.2 ^ e) (pow_zero _), pow_one,
      smul_eq_mul]
  · intro e he
    rw [Function.mem_support] at he
    by_contra hne
    apply he
    have hz : coeff (Finsupp.single q 1) (e.prod fun s n => (fun p : Fin m × Fin d => a p.1 p.2) s ^ n) = 0 := by
      rcases Nat.lt_or_ge e.degree 2 with hd | hd
      · rcases Nat.lt_or_ge e.degree 1 with hd1 | hd1
        · have he0 : e = 0 := by
            have : e.degree = 0 := by omega
            exact (Finsupp.degree_eq_zero_iff e).1 this
          rw [he0, Finsupp.prod_zero_index, coeff_one, if_neg]
          exact Finsupp.single_ne_zero.2 one_ne_zero
        · obtain ⟨p, rfl⟩ := degree_eq_one e (by omega)
          exact absurd (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ p))) hne
      · have hl := low_P hlow e
        exact hl _ (by rw [Finsupp.degree_single]; omega)
    rw [hz, smul_zero]

theorem coeff_X_single {n : ℕ} (q p : Fin n × Fin d) :
    coeff (Finsupp.single q 1) (X p : PS R n d) = if q = p then 1 else 0 := by
  classical
  rw [coeff_X]
  by_cases h : q = p
  · simp [h]
  · rw [if_neg, if_neg h]
    intro h'
    exact h (Finsupp.single_left_injective one_ne_zero h')

theorem formal_group_coeff_second_linear (G : FGLaw R d) (i l : Fin d) :
    coeff (Finsupp.single ((1 : Fin 2), l) 1) (G.F i) = if l = i then 1 else 0 := by
  classical
  have e := congrArg (coeff (Finsupp.single ((0 : Fin 1), l) 1)) (G.unit i)
  rw [coeff_lin_ev _ (by
      intro j i'
      fin_cases j
      · simp
      · simp [pt]), coeff_X_single] at e
  rw [Fintype.sum_prod_type, Fin.sum_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, map_zero, mul_zero,
    Finset.sum_const_zero, zero_add, pt, coeff_X_single] at e
  simp only [Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true] at e
  rw [e]

theorem formal_group_coeff_first_linear (G : FGLaw R d) (i l : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), l) 1) (G.F i) = if l = i then 1 else 0 := by
  classical
  have e := congrArg (coeff (Finsupp.single ((0 : Fin 2), l) 1)) (G.comm i)
  rw [coeff_lin_ev _ (by
      intro j i'
      fin_cases j <;> simp [pt])] at e
  rw [Fintype.sum_prod_type, Fin.sum_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pt, coeff_X_single] at e
  simp only [Prod.mk.injEq, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff, false_and, if_false, mul_zero,
    Finset.sum_const_zero, zero_add, true_and, mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    OfNat.ofNat_ne_one, one_ne_zero, zero_ne_one] at e
  rw [← e, formal_group_coeff_second_linear]

end Lin

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
