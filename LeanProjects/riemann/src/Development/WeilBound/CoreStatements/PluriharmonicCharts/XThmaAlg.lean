import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.SymExp

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.thma_alg

noncomputable def pml {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → σ) → ℝ) :
    MultilinearMap ℝ (fun _ : Fin n => σ → ℝ) ℝ :=
  ∑ w : Fin n → σ, a w • (MultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compLinearMap
    (fun r => LinearMap.proj (w r))

theorem pml_apply {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → σ) → ℝ) (c : Fin n → σ → ℝ) :
    pml n a c = polar n a c := by
  simp [pml, polar, MultilinearMap.sum_apply, mul_comm]

theorem pml_symm {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → σ) → ℝ)
    (ha : ∀ (π : Equiv.Perm (Fin n)) w, a (w ∘ π) = a w) : IsSymmForm (pml n a) := by
  intro π v
  rw [pml_apply, pml_apply]
  unfold polar
  refine Fintype.sum_equiv (π.arrowCongr (Equiv.refl σ)) _ _ ?_
  intro w
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, Function.id_comp]
  congr 1
  · exact Fintype.prod_equiv π _ _ (fun r => by simp)
  · have h := ha π (w ∘ π.symm)
    simp only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] at h
    rw [h]
    congr 1

theorem eval_formPoly {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → σ) → ℝ) (c : σ → ℝ) :
    MvPolynomial.eval c (formPoly n a) = polar n a fun _ => c := by
  unfold formPoly polar
  simp [mul_comm]

theorem eval_expand {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → σ) → ℝ)
    (ha : ∀ (π : Equiv.Perm (Fin n)) w, a (w ∘ π) = a w) (c e : σ → ℝ) (t : ℝ) :
    MvPolynomial.eval (fun x => c x + t * e x) (formPoly n a) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * t ^ j * polar n a (mix j e c) := by
  have h := symm_expand (pml n a) (pml_symm n a ha) e c t
  simp only [pml_apply] at h
  have hc : (fun x => c x + t * e x) = c + t • e := by
    funext x
    simp
  rw [hc, eval_formPoly]
  exact h

theorem eval_linePoly {σ : Type} (c : σ → ℝ) (e : σ → ℤ) (Q : MvPolynomial σ ℝ) (u : ℝ) :
    (linePoly c e Q).eval u = MvPolynomial.eval (fun x => c x + (-u / 2) * (e x : ℝ)) Q := by
  unfold linePoly
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.eval_mul, hp, aeval_X, MvPolynomial.eval_X, Polynomial.eval_sub,
      Polynomial.eval_C, Polynomial.eval_X]
    congr 1
    ring

theorem linePoly_formPoly {σ : Type} [Fintype σ] (D : ℕ) (b : (Fin D → σ) → ℝ)
    (hb : ∀ (π : Equiv.Perm (Fin D)) w, b (w ∘ π) = b w) (c : σ → ℝ) (e : σ → ℤ) :
    linePoly c e (formPoly D b) =
      volPoly D fun j => (1 / 2) ^ j * polar D b (mix j (fun x => (e x : ℝ)) c) := by
  apply Polynomial.funext
  intro u
  rw [eval_linePoly, eval_expand D b hb, volPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_X]
  rw [show -u / 2 = 1 / 2 * -u by ring, mul_pow]
  ring

open Classical in

noncomputable def mixPoly {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → σ) → ℝ) (k : ℕ) (e : σ → ℝ) (a₀ : σ) :
    MvPolynomial σ ℝ :=
  ∑ w : Fin n → σ, (∏ r : Fin n, if (r : ℕ) < k then C (e (w r)) else if w r = a₀ then 0 else X (w r)) * C (a w)

open Classical in
theorem eval_mixPoly {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → σ) → ℝ) (k : ℕ) (e : σ → ℝ) (a₀ : σ)
    (c : σ → ℝ) :
    MvPolynomial.eval c (mixPoly n a k e a₀) = polar n a (mix k e fun x => if x = a₀ then 0 else c x) := by
  simp only [mixPoly, polar, mix, map_sum, map_mul, map_prod, MvPolynomial.eval_C]
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun r _ => ?_
  by_cases h1 : (r : ℕ) < k <;> by_cases h2 : w r = a₀ <;> simp [h1, h2]

theorem int_to_real {σ : Type} [Fintype σ] (n m : ℕ) (a : (Fin n → σ) → ℝ) (b : (Fin m → σ) → ℝ) (k l : ℕ)
    (e : σ → ℝ) (a₀ : σ) (t : ℝ)
    (h : ∀ z : σ → ℤ, z a₀ = 0 → polar n a (mix k e fun x => (z x : ℝ)) = t * polar m b (mix l e fun x => (z x : ℝ)))
    (c : σ → ℝ) (hc : c a₀ = 0) : polar n a (mix k e c) = t * polar m b (mix l e c) := by
  classical
  have key : mixPoly n a k e a₀ = C t * mixPoly m b l e a₀ := by
    refine MvPolynomial.funext_set (fun _ => Set.range (Int.cast : ℤ → ℝ))
      (fun _ => Set.infinite_range_of_injective Int.cast_injective) ?_
    intro x hx
    choose z hz using fun i => hx i (Set.mem_univ i)
    have hx' : x = fun i => (z i : ℝ) := funext fun i => (hz i).symm
    subst hx'
    rw [map_mul, eval_C, eval_mixPoly, eval_mixPoly]
    have h' := h (fun i => if i = a₀ then 0 else z i) (by simp)
    have hf : (fun x => if x = a₀ then (0 : ℝ) else (z x : ℝ)) =
        fun x => (((if x = a₀ then 0 else z x : ℤ)) : ℝ) := by
      funext i
      split_ifs <;> simp
    simpa only [hf] using h'
  have h' := congrArg (MvPolynomial.eval c) key
  rw [map_mul, eval_C, eval_mixPoly, eval_mixPoly] at h'
  have hc' : (fun x => if x = a₀ then (0 : ℝ) else c x) = c := by
    funext x
    split_ifs with hx
    · rw [hx, hc]
    · rfl
  simpa only [hc'] using h'

end PositivityTheory.Xgp.thma_alg

private theorem succ_mul_choose_odd_eq_choose_succ_mul (D m : ℕ) :
    ((D : ℝ) + 1) * (D.choose (2 * m + 1) : ℝ) = ((D + 1).choose (2 * m + 2) : ℝ) * (2 * m + 2) := by
  have h := Nat.add_one_mul_choose_eq D (2 * m + 1)
  have h' : (((D + 1) * D.choose (2 * m + 1) : ℕ) : ℝ) = (((D + 1).choose (2 * m + 1 + 1) * (2 * m + 1 + 1) : ℕ) : ℝ) := by
    rw [h]
  push_cast at h'
  linear_combination h'

theorem PositivityTheory.Xgp.t_thma_alg : ∀ (σ : Type) [Fintype σ] (D : ℕ) (a : (Fin (D + 1) → σ) → ℝ) (b : (Fin D → σ) → ℝ) (κ : ℕ → ℝ) (ε : σ → ℤ) (a₀ : σ), (∀ (π : Equiv.Perm (Fin (D + 1))) w, a (w ∘ π) = a w) → (∀ (π : Equiv.Perm (Fin D)) w, b (w ∘ π) = b w) → (∀ n : σ → ℤ, n a₀ = 0 → polar (D + 1) a (fun _ x => (n x : ℝ)) = 0 ∧ ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D + 1 → polar (D + 1) a (mix (2 * k) (fun x => (ε x : ℝ)) fun x => (n x : ℝ)) = -(2 * κ k) * polar D b (mix (2 * k - 1) (fun x => (ε x : ℝ)) fun x => (n x : ℝ))) → ∀ (c : σ → ℝ), c a₀ = 0 → ∀ u : ℝ, eval (fun x => c x - u / 2 * ε x) (formPoly (D + 1) a) + eval (fun x => c x + u / 2 * ε x) (formPoly (D + 1) a) = (tsgPoly D κ (linePoly c ε (formPoly D b))).eval u := by
  intro σ _ D a b κ ε a₀ ha hb hint c hc u
  have hP0 : polar (D + 1) a (mix 0 (fun x => (ε x : ℝ)) c) = 0 := by
    have h := PositivityTheory.Xgp.thma_alg.int_to_real (D + 1) D a b 0 0 (fun x => (ε x : ℝ)) a₀ 0
      (fun z hz => by
        have h0 := (hint z hz).1
        rw [zero_mul]
        convert h0 using 2
        funext i
        simp [mix]) c hc
    simpa using h
  have hPk : ∀ m : ℕ, 2 * m + 1 < D + 1 →
      polar (D + 1) a (mix (2 * m + 2) (fun x => (ε x : ℝ)) c) =
        -(2 * κ (m + 1)) * polar D b (mix (2 * m + 1) (fun x => (ε x : ℝ)) c) := by
    intro m hm
    refine PositivityTheory.Xgp.thma_alg.int_to_real (D + 1) D a b (2 * m + 2) (2 * m + 1) (fun x => (ε x : ℝ)) a₀ _
      (fun z hz => ?_) c hc
    have h1 := (hint z hz).2 (m + 1) (by omega) (by omega)
    have e1 : 2 * (m + 1) = 2 * m + 2 := by ring
    rw [e1] at h1
    have e2 : 2 * m + 2 - 1 = 2 * m + 1 := by omega
    rw [e2] at h1
    exact h1
  have h1 : MvPolynomial.eval (fun x => c x + (-(u / 2)) * (ε x : ℝ)) (formPoly (D + 1) a) = _ :=
    PositivityTheory.Xgp.thma_alg.eval_expand (D + 1) a ha c (fun x => (ε x : ℝ)) (-(u / 2))
  have h2 : MvPolynomial.eval (fun x => c x + (u / 2) * (ε x : ℝ)) (formPoly (D + 1) a) = _ :=
    PositivityTheory.Xgp.thma_alg.eval_expand (D + 1) a ha c (fun x => (ε x : ℝ)) (u / 2)
  have e : (fun x => c x - u / 2 * (ε x : ℝ)) = fun x => c x + (-(u / 2)) * (ε x : ℝ) := by
    funext x
    ring
  rw [e, h1, h2, ← Finset.sum_add_distrib]
  have hx : ∀ j : ℕ, (-Polynomial.X : Polynomial ℝ) ^ j = Polynomial.C ((-1) ^ j) * Polynomial.X ^ j := by
    intro j
    rw [neg_pow]
    simp
  have hcoeff : ∀ n, (linePoly c ε (formPoly D b)).coeff n =
      if n < D + 1 then (D.choose n : ℝ) * ((1 / 2) ^ n * polar D b (mix n (fun x => (ε x : ℝ)) c)) * (-1) ^ n
      else 0 := by
    intro n
    rw [PositivityTheory.Xgp.thma_alg.linePoly_formPoly D b hb c ε]
    simp only [volPoly, Polynomial.finset_sum_coeff, hx, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp [Finset.mem_range]
  rw [tsgPoly, Polynomial.eval_finset_sum]
  set Pl := linePoly c ε (formPoly D b) with hPl
  have key : ∀ f : ℕ → ℝ, (∀ n, Pl.coeff n = 0 → f n = 0) →
      ∑ n ∈ Finset.range (Pl.natDegree + 1), f n = ∑ n ∈ Finset.range (D + 1), f n := by
    intro f hf
    have hbig : ∀ n, D + 1 ≤ n → Pl.coeff n = 0 := by
      intro n hn
      rw [hcoeff, if_neg (by omega)]
    rw [Finset.sum_subset (Finset.range_mono (Nat.le_add_right (Pl.natDegree + 1) (D + 1)))
        (fun n hn hn' => hf n (Polynomial.coeff_eq_zero_of_natDegree_lt (by simp at hn hn'; omega))),
      Finset.sum_subset (Finset.range_mono (Nat.le_add_left (D + 1) (Pl.natDegree + 1)))
        (fun n hn hn' => hf n (hbig n (by simp at hn hn'; omega)))]
  rw [key]
  swap
  · intro n hn
    split_ifs <;> simp [hn]
  rw [Finset.sum_range_succ', hP0]
  simp only [mul_zero, add_zero]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_range] at hn
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have hno : ¬ Odd (m + m) := Nat.not_odd_iff_even.mpr ⟨m, rfl⟩
    rw [if_neg hno, Odd.neg_pow ⟨m, by ring⟩]
    simp
  · have e1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    have e2 : 2 * m + 1 + 1 = 2 * m + 2 := by ring
    rw [if_pos (odd_two_mul_add_one m), e1, hcoeff, if_pos hn, e2, hPk m hn, Even.neg_pow ⟨m + 1, by ring⟩]
    have hch := succ_mul_choose_odd_eq_choose_succ_mul D m
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    push_cast
    have hneg : ((-1 : ℝ)) ^ (2 * m + 1) = -1 := by
      rw [pow_succ, pow_mul]
      norm_num
    have hh : (1 / 2 : ℝ) ^ (2 * m + 2) = (1 / 2) ^ (2 * m + 1) * (1 / 2) := pow_succ _ _
    have hu : (u / 2) ^ (2 * m + 2) = u ^ (2 * m + 2) * (1 / 2 : ℝ) ^ (2 * m + 2) := by
      rw [← mul_pow]
      ring
    rw [hu, hh, hneg]
    have hm : (m : ℝ) + 1 ≠ 0 := by positivity
    generalize (1 / 2 : ℝ) ^ (2 * m + 1) = h
    generalize u ^ (2 * m + 2) = U
    generalize polar D b (mix (2 * m + 1) (fun x => (ε x : ℝ)) c) = Q
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hm]
    linear_combination (κ (m + 1) * h * Q * U) * hch
