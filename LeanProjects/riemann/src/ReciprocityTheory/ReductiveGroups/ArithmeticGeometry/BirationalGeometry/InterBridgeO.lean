import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeJ
import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory

def NormPolyStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (f : MRing ι) (a : K → ℕ),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → IsMultiHomog f a → f ∉ P →
    ∃ (c : MvPolynomial (Fin (e + 1)) ℂ) (m : ℕ), c ≠ 0 ∧ c.IsHomogeneous m ∧
      ∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) f) = 0 → eval (Ψ (segre z)) c = 0

theorem eval_smul_of_isHomogeneous {n : ℕ} {c : MvPolynomial (Fin n) ℂ} {m : ℕ}
    (hc : c.IsHomogeneous m) (t : ℂ) (v : Fin n → ℂ) :
    eval (fun i => t * v i) c = t ^ m * eval v c := by
  conv_lhs => rw [c.as_sum]
  conv_rhs => rw [c.as_sum]
  simp only [map_sum, Finset.mul_sum, eval_monomial]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = m := by
    have h1 := hc (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h1
  simp only [mul_pow, Finsupp.prod_mul]
  rw [show (d.prod fun _ e => t ^ e) = t ^ m by
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, hdeg]]
  ring

theorem exists_eval_cons_ne_zero {n : ℕ} {c : MvPolynomial (Fin (n + 1)) ℂ} {m : ℕ}
    (hc0 : c ≠ 0) (hc : c.IsHomogeneous m) : ∃ y : Fin n → ℂ, eval (Fin.cons 1 y) c ≠ 0 := by
  by_contra h
  push_neg at h
  apply hc0
  have hX : (X 0 : MvPolynomial (Fin (n + 1)) ℂ) * c = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, eval_X, map_zero]
    by_cases hx : x 0 = 0
    · rw [hx, zero_mul]
    · have hxe : x = fun i => x 0 * (Fin.cons 1 (fun j => x j.succ / x 0) : Fin (n + 1) → ℂ) i := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · rw [Fin.cons_succ, mul_div_left_comm, div_self hx, mul_one]
      have hx0 : eval x c = 0 := by
        rw [hxe, eval_smul_of_isHomogeneous hc (x 0) (Fin.cons 1 (fun j => x j.succ / x 0)), h,
          mul_zero]
      rw [hx0, mul_zero]
  rcases mul_eq_zero.mp hX with h0 | h0
  · exact absurd h0 (X_ne_zero 0)
  · exact h0

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

private theorem volume_eval_eq_zero_lemma :
    ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℂ), p ≠ 0 → volume {y : Fin n → ℂ | eval y p = 0} = 0 := by
  intro n
  induction n with
  | zero =>
    intro p hp
    refine measure_mono_null (fun y hy => ?_) measure_empty
    exfalso
    apply hp
    apply MvPolynomial.funext
    intro x
    have hxy : x = y := Subsingleton.elim _ _
    subst hxy
    simpa using hy
  | succ n ih =>
    intro p hp
    have hq0 : finSuccEquiv ℂ n p ≠ 0 := by
      intro h
      apply hp
      apply (finSuccEquiv ℂ n).injective
      rw [h, map_zero]
    have hbad := ih _ (Polynomial.leadingCoeff_ne_zero.mpr hq0)
    let E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0
    have hE : MeasurePreserving E (Measure.pi fun _ => (volume : Measure ℂ))
        ((volume : Measure ℂ).prod (Measure.pi fun _ : Fin n => (volume : Measure ℂ))) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℂ)) 0
    have hC : MeasurableSet {y : Fin (n + 1) → ℂ | eval y p = 0} :=
      (isClosed_eq (MvPolynomial.continuous_eval p) continuous_const).measurableSet
    have hT : MeasurableSet (E.symm ⁻¹' {y : Fin (n + 1) → ℂ | eval y p = 0}) :=
      E.symm.measurable hC
    have hS : {y : Fin (n + 1) → ℂ | eval y p = 0} =
        E ⁻¹' (E.symm ⁻¹' {y : Fin (n + 1) → ℂ | eval y p = 0}) := by
      ext x
      simp only [Set.mem_preimage, MeasurableEquiv.symm_apply_apply]
    show (Measure.pi fun _ => (volume : Measure ℂ)) _ = 0
    rw [hS, hE.measure_preimage_equiv, Measure.prod_apply_symm hT]
    have hae : ∀ᵐ s ∂(Measure.pi fun _ : Fin n => (volume : Measure ℂ)),
        eval s (finSuccEquiv ℂ n p).leadingCoeff ≠ 0 :=
      ae_iff.2 (by
        have hbad' : (Measure.pi fun _ : Fin n => (volume : Measure ℂ))
            {y | eval y (finSuccEquiv ℂ n p).leadingCoeff = 0} = 0 := hbad
        simpa using hbad')
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hae] with s hs
    have hmap : (finSuccEquiv ℂ n p).map (eval s) ≠ 0 := by
      intro h0
      apply hs
      have h1 := congrArg (fun r => Polynomial.coeff r (finSuccEquiv ℂ n p).natDegree) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h1
      exact h1
    refine Set.Finite.measure_zero
      ((((finSuccEquiv ℂ n p).map (eval s)).roots.toFinset.finite_toSet).subset ?_) _
    intro y hy
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hy
    have hcons : E.symm (y, s) = Fin.cons y s := by
      (simp [E, Fin.insertNth_zero']) <;> rfl
    rw [hcons, eval_eq_eval_mv_eval'] at hy
    simpa [Polynomial.mem_roots hmap] using hy

theorem projB_null_of (hN : NormPolyStatement)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hJ : IsMultiHomogIdeal J) (hJP : ¬ J ≤ P) :
    volume {y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} = 0 := by
  obtain ⟨S, hS, rfl⟩ := hJ
  obtain ⟨f, hfS, hfP⟩ : ∃ f ∈ S, f ∉ P := by
    by_contra h
    push_neg at h
    exact hJP (Ideal.span_le.2 h)
  obtain ⟨a, ha⟩ := hS f hfS
  obtain ⟨c, m, hc0, hc, hz⟩ := hN K ι P e Ψ f a hP hΨ ha hfP
  have key : ∀ y : Fin e → ℂ,
      eval y (Polynomial.eval 1 (finSuccEquiv ℂ e c)) = eval (Fin.cons 1 y) c := by
    intro y
    rw [eval_eq_eval_mv_eval', Polynomial.eval_map, Polynomial.eval₂_at_one]
  have hp0 : Polynomial.eval 1 (finSuccEquiv ℂ e c) ≠ 0 := by
    obtain ⟨y, hy⟩ := exists_eval_cons_ne_zero hc0 hc
    intro h0
    apply hy
    rw [← key, h0, map_zero]
  refine measure_mono_null ?_ (volume_eval_eq_zero_lemma e _ hp0)
  rintro y ⟨z, hzP, hzJ, hzy⟩
  have hzJ' : (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧
      ∀ g ∈ Ideal.span S, eval z (map (Int.castRingHom ℂ) g) = 0 := hzJ
  show eval y (Polynomial.eval 1 (finSuccEquiv ℂ e c)) = 0
  rw [key, ← hzy]
  exact hz z hzP (hzJ'.2 f (Ideal.subset_span hfS))

end ReciprocityTheory.ChartRestriction.G.Geo
