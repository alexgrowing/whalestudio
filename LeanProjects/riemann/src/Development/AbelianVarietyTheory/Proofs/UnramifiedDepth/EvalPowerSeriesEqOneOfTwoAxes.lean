import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AlphaPair

section TwoAxes

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {d : ℕ}

theorem axes_monomial_sub_mem (I : Ideal A) (a : Fin d → A) (ha : ∀ j, a j ∈ I) (m : Fin d → ℕ) :
    (∏ j, a j ^ m j) - ∏ j, (0 : A) ^ m j ∈ I := by
  rw [← Ideal.Quotient.eq]
  simp only [map_prod, map_pow, Ideal.Quotient.eq_zero_iff_mem.2 (ha _), map_zero]

theorem axes_mul_eq_zero {e x y : A} (he : e ^ 2 = 0) (hx : x ∈ Ideal.span {e}) (hy : y ∈ Ideal.span {e}) :
    x * y = 0 := by
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  linear_combination (u * v) * he

theorem evalPoints_second_difference (f : PS R 3 d) {e : A} (he : e ^ 2 = 0) (a a' b : Fin d → A)
    (ha : ∀ j, a j ∈ Ideal.span {e}) (ha' : ∀ j, a' j ∈ Ideal.span {e}) (hb : ∀ j, IsNilpotent (b j)) :
    evP ![a, a', b] f + evP ![0, 0, b] f = evP ![0, a', b] f + evP ![a, 0, b] f := by
  obtain ⟨N, hN0, hN⟩ := evBasic_exists_pow b hb
  have sq : ∀ x ∈ Ideal.span {e}, x ^ (N + 2) = 0 := fun x hx => by
    rw [pow_add, sq, axes_mul_eq_zero he hx hx, mul_zero]
  have key : ∀ c c' : Fin d → A, (∀ j, c j ∈ Ideal.span {e}) → (∀ j, c' j ∈ Ideal.span {e}) →
      evP ![c, c', b] f = ReciprocityTheory.PGsh.Be2.tEval (N + 2) f
        (fun q : Fin 3 × Fin d => ![c, c', b] q.1 q.2) := fun c c' hc hc' => by
    refine evBasic_nEval_eq_tEval f _ (N + 2) ?_
    rintro ⟨i, j⟩
    fin_cases i
    · exact sq _ (hc j)
    · exact sq _ (hc' j)
    · show b j ^ (N + 2) = 0
      rw [pow_add, hN, zero_mul]
  have h0 : ∀ j, (0 : Fin d → A) j ∈ Ideal.span {e} := fun _ => Ideal.zero_mem _
  rw [key a a' ha ha', key 0 0 h0 h0, key 0 a' h0 ha', key a 0 ha h0]
  unfold ReciprocityTheory.PGsh.Be2.tEval
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Fintype.prod_prod_type, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply]
  have h := axes_mul_eq_zero he (axes_monomial_sub_mem _ a ha fun j => m (0, j))
    (axes_monomial_sub_mem _ a' ha' fun j => m (1, j))
  rw [← mul_add, ← mul_add]
  congr 1
  linear_combination (∏ j, b j ^ (m (2, j) : ℕ)) * h

theorem evalPoints_eval_axis {u v : Fin d → PS R 2 d} {f : PS R 3 d}
    (hu : ∀ j, MvPowerSeries.constantCoeff (u j) = 0) (hv : ∀ j, MvPowerSeries.constantCoeff (v j) = 0)
    (h : ev (n := 2) ![u, v, pt R d 1] f = 1) (c b : Fin d → A)
    (hc : ∀ j, IsNilpotent (c j)) (hb : ∀ j, IsNilpotent (b j)) (x y : Fin d → A)
    (hx : ∀ j, evP ![c, b] (u j) = x j) (hy : ∀ j, evP ![c, b] (v j) = y j) :
    evP ![x, y, b] f = 1 := by
  have hn : ∀ q : Fin 2 × Fin d, IsNilpotent (![c, b] q.1 q.2) := by
    rintro ⟨i, j⟩
    fin_cases i
    · exact hc j
    · exact hb j
  have h1 := congrArg (evP ![c, b]) h
  unfold evP ev at h1
  rw [nEval_one hn, ChartCompare.nEval_subst _ _ _ _ hn] at h1
  · rw [← h1]
    unfold evP
    congr 1
    funext ⟨i, j⟩
    fin_cases i
    · exact (hx j).symm
    · exact (hy j).symm
    · exact (ChartCompare.nEval_X (R₀ := R) _ hn ((1 : Fin 2), j)).symm
  · rintro ⟨i, j⟩
    fin_cases i
    · exact hu j
    · exact hv j
    · exact MvPowerSeries.constantCoeff_X _

end TwoAxes

theorem evalPoints_eq_one_of_two_axes : ∀ (R : Type) [CommRing R] (d : ℕ) (ph : PS R 3 d), ev (n := 2) ![0, pt R d 0, pt R d 1] ph = 1 → ev (n := 2) ![pt R d 0, 0, pt R d 1] ph = 1 → ∀ (A : Type) [CommRing A] [Algebra R A] (e : A), e ^ 2 = 0 → ∀ a a' b : Fin d → A, (∀ j, a j ∈ Ideal.span {e}) → (∀ j, a' j ∈ Ideal.span {e}) → (∀ j, IsNilpotent (b j)) → evP ![a, a', b] ph = 1 := by
  intro R _ d ph h₁ h₂ A _ _ e he a a' b ha ha' hb
  have nil : ∀ c : Fin d → A, (∀ j, c j ∈ Ideal.span {e}) → ∀ j, IsNilpotent (c j) := fun c hc j =>
    ⟨2, by rw [sq, axes_mul_eq_zero he (hc j) (hc j)]⟩
  have hn : ∀ c : Fin d → A, (∀ j, c j ∈ Ideal.span {e}) →
      ∀ q : Fin 2 × Fin d, IsNilpotent (![c, b] q.1 q.2) := by
    rintro c hc ⟨i, j⟩
    fin_cases i
    · exact nil c hc j
    · exact hb j
  have e₁ : ∀ c : Fin d → A, (∀ j, c j ∈ Ideal.span {e}) → evP ![0, c, b] ph = 1 := fun c hc =>
    evalPoints_eval_axis (fun _ => map_zero _) (fun _ => MvPowerSeries.constantCoeff_X _) h₁ c b (nil c hc) hb 0 c
      (fun _ => ChartCompare.nEval_zero _ (hn c hc))
      (fun j => ChartCompare.nEval_X (R₀ := R) _ (hn c hc) ((0 : Fin 2), j))
  have e₂ : evP ![a, 0, b] ph = 1 :=
    evalPoints_eval_axis (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => map_zero _) h₂ a b (nil a ha) hb a 0
      (fun j => ChartCompare.nEval_X (R₀ := R) _ (hn a ha) ((0 : Fin 2), j))
      (fun _ => ChartCompare.nEval_zero _ (hn a ha))
  have h := evalPoints_second_difference ph he a a' b ha ha' hb
  rw [e₁ a' ha', e₂, e₁ 0 fun _ => Ideal.zero_mem _] at h
  exact add_right_cancel h

end GlobalTheory.AlphaPair
end
