import Mathlib
open MeasureTheory

namespace GlobalTheory.CompanionTheory.AePoly

theorem ae_eval_ne_zero_fin : ∀ (d : ℕ) (Q : MvPolynomial (Fin d) ℂ), Q ≠ 0 →
    ∀ᵐ x ∂(volume : Measure (Fin d → ℂ)), MvPolynomial.eval x Q ≠ 0 := by
  intro d
  induction d with
  | zero =>
    intro Q hQ
    have hex : ∃ x : Fin 0 → ℂ, MvPolynomial.eval x Q ≠ 0 := by
      by_contra h
      push Not at h
      exact hQ (MvPolynomial.funext fun x => by simpa using h x)
    obtain ⟨x, hx⟩ := hex
    refine Filter.Eventually.of_forall fun y => ?_
    rwa [Subsingleton.elim y x]
  | succ d ih =>
    intro Q hQ
    have hP0 : MvPolynomial.finSuccEquiv ℂ d Q ≠ 0 :=
      (map_ne_zero_iff _ (MvPolynomial.finSuccEquiv ℂ d).injective).2 hQ
    have hlc := ih _ (Polynomial.leadingCoeff_ne_zero.2 hP0)
    have hF : Continuous fun z : ℂ × (Fin d → ℂ) => (Fin.cons z.1 z.2 : Fin (d + 1) → ℂ) := by
      refine continuous_pi fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using continuous_fst
      · simpa using (by fun_prop : Continuous fun a : ℂ × (Fin d → ℂ) => a.2 j)
    have hS : MeasurableSet
        {z : ℂ × (Fin d → ℂ) | MvPolynomial.eval (Fin.cons z.1 z.2 : Fin (d + 1) → ℂ) Q = 0} :=
      (isClosed_eq ((MvPolynomial.continuous_eval Q).comp hF) continuous_const).measurableSet
    have hprod : ∀ᵐ z ∂((volume : Measure ℂ).prod (volume : Measure (Fin d → ℂ))),
        MvPolynomial.eval (Fin.cons z.1 z.2 : Fin (d + 1) → ℂ) Q ≠ 0 := by
      rw [ae_iff]
      simp only [ne_eq, not_not]
      rw [Measure.prod_apply_symm hS]
      have hz : (fun s : Fin d → ℂ => (volume : Measure ℂ) ((fun y => (y, s)) ⁻¹'
          {z : ℂ × (Fin d → ℂ) | MvPolynomial.eval (Fin.cons z.1 z.2 : Fin (d + 1) → ℂ) Q = 0}))
          =ᵐ[volume] 0 := by
        refine hlc.mono fun s hs => ?_
        have hR : (MvPolynomial.finSuccEquiv ℂ d Q).map (MvPolynomial.eval s) ≠ 0 := by
          intro h0
          apply hs
          have := congrArg (fun p => Polynomial.coeff p
            (MvPolynomial.finSuccEquiv ℂ d Q).natDegree) h0
          simpa [Polynomial.coeff_map] using this
        refine measure_mono_null ?_ ((Polynomial.finite_setOf_isRoot hR).measure_zero volume)
        intro y hy
        simpa [Polynomial.IsRoot, MvPolynomial.eval_eq_eval_mv_eval'] using hy
      rw [lintegral_congr_ae hz]
      simp
    have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℂ) 0).quasiMeasurePreserving.ae hprod
    filter_upwards [h] with x hx
    have hc : (Fin.cons (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℂ) 0 x).1
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℂ) 0 x).2 : Fin (d + 1) → ℂ) = x := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [MeasurableEquiv.piFinSuccAbove, Fin.tail]
    rwa [hc] at hx

theorem measurePreserving_uncurry (M n : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin M) (Fin n) ℂ).symm
      (volume : Measure (Fin M → Fin n → ℂ)) (volume : Measure (Fin M × Fin n → ℂ)) := by
  refine ⟨(MeasurableEquiv.curry (Fin M) (Fin n) ℂ).symm.measurable, ?_⟩
  refine (Measure.pi_eq (μ := fun _ : Fin M × Fin n => (volume : Measure ℂ)) fun s hs => ?_).symm
  rw [MeasurableEquiv.map_apply]
  have h : (MeasurableEquiv.curry (Fin M) (Fin n) ℂ).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun a => Set.univ.pi fun k => s (a, k) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Prod.forall]
    rfl
  rw [h, volume_pi, Measure.pi_pi]
  simp_rw [volume_pi, Measure.pi_pi]
  rw [← Fintype.prod_prod_type']

theorem ae_eval_matrix_ne_zero : ∀ (M n : ℕ) (Q : MvPolynomial (Fin M × Fin n) ℂ), Q ≠ 0 →
    ∀ᵐ C ∂(volume : Measure (Fin M → Fin n → ℂ)), MvPolynomial.eval (fun p => C p.1 p.2) Q ≠ 0 := by
  intro M n Q hQ
  have hQ' : MvPolynomial.rename (finProdFinEquiv : Fin M × Fin n ≃ Fin (M * n)) Q ≠ 0 :=
    (map_ne_zero_iff _ (MvPolynomial.rename_injective _ finProdFinEquiv.injective)).2 hQ
  have h1 := ae_eval_ne_zero_fin _ _ hQ'
  have h2 := (volume_measurePreserving_piCongrLeft (fun _ : Fin (M * n) => ℂ)
    (finProdFinEquiv : Fin M × Fin n ≃ Fin (M * n))).quasiMeasurePreserving.ae h1
  have h3 := (measurePreserving_uncurry M n).quasiMeasurePreserving.ae h2
  filter_upwards [h3] with C hC
  rw [MvPolynomial.eval_rename] at hC
  have hfun : (MeasurableEquiv.piCongrLeft (fun _ : Fin (M * n) => ℂ)
      (finProdFinEquiv : Fin M × Fin n ≃ Fin (M * n))
      ((MeasurableEquiv.curry (Fin M) (Fin n) ℂ).symm C)) ∘ finProdFinEquiv =
      fun p => C p.1 p.2 := by
    funext p
    simp only [Function.comp]
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    rfl
  rwa [hfun] at hC

end GlobalTheory.CompanionTheory.AePoly
