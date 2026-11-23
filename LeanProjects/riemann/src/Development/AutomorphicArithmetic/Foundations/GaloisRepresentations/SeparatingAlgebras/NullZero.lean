import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private lemma pt_coe {n : ℕ} (θ : Fin n → UnitAddCircle) (i : Fin n) :
    ((pt θ i : ℂˣ) : ℂ) = ((AddCircle.toCircle (θ i) : Circle) : ℂ) := rfl

private lemma eval_cons_pt {n : ℕ} (s : UnitAddCircle) (θ : Fin n → UnitAddCircle)
    (p : MvPolynomial (Fin (n + 1)) ℂ) :
    MvPolynomial.eval (fun i => (pt (Fin.cons s θ : Fin (n + 1) → UnitAddCircle) i : ℂ)) p =
      Polynomial.eval ((AddCircle.toCircle s : Circle) : ℂ)
        (Polynomial.map (MvPolynomial.eval (fun i => (pt θ i : ℂ))) (MvPolynomial.finSuccEquiv ℂ n p)) := by
  rw [← MvPolynomial.eval_eq_eval_mv_eval']
  have h : (fun i => (pt (Fin.cons s θ : Fin (n + 1) → UnitAddCircle) i : ℂ)) =
      (Fin.cons ((AddCircle.toCircle s : Circle) : ℂ) (fun i => (pt θ i : ℂ)) : Fin (n + 1) → ℂ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [pt_coe]
  rw [h]

private lemma continuous_eval_pt {n : ℕ} (p : MvPolynomial (Fin n) ℂ) :
    Continuous fun θ : Fin n → UnitAddCircle => MvPolynomial.eval (fun i => (pt θ i : ℂ)) p := by
  have h1 : Continuous fun x : Fin n → ℂ => MvPolynomial.eval x p := MvPolynomial.continuous_eval p
  have h2 : Continuous fun θ : Fin n → UnitAddCircle => (fun i => (pt θ i : ℂ)) := by
    refine continuous_pi fun i => ?_
    simp only [pt_coe]
    exact continuous_subtype_val.comp ((AddCircle.continuous_toCircle).comp (continuous_apply i))
  exact h1.comp h2

private lemma circle_zero_null (r : Polynomial ℂ) (hr : r ≠ 0) :
    volume {s : UnitAddCircle | r.eval ((AddCircle.toCircle s : Circle) : ℂ) = 0} = 0 := by
  haveI : NullSingletonClass (volume : Measure UnitAddCircle) := ⟨fun x => by
    have h := AddCircle.volume_closedBall (T := (1 : ℝ)) (x := x) 0
    simpa using h⟩
  have hinj : Function.Injective fun s : UnitAddCircle => ((AddCircle.toCircle s : Circle) : ℂ) :=
    Circle.coe_injective.comp (AddCircle.injective_toCircle one_ne_zero)
  have hfin : ({s : UnitAddCircle | r.eval ((AddCircle.toCircle s : Circle) : ℂ) = 0}).Finite := by
    refine Set.Finite.of_finite_image (f := fun s : UnitAddCircle => ((AddCircle.toCircle s : Circle) : ℂ)) ?_ hinj.injOn
    refine (Polynomial.finite_setOf_isRoot hr).subset ?_
    rintro _ ⟨s, hs, rfl⟩
    exact hs
  exact hfin.measure_zero _

theorem UpperTheory.Gal.Gen.nullZero_pf :
    UpperTheory.Gal.Gen.NullZero := by
  intro n
  induction n with
  | zero =>
    intro p hp
    obtain ⟨a, rfl⟩ : ∃ a, p = MvPolynomial.C a := ⟨_, MvPolynomial.eq_C_of_isEmpty p⟩
    have ha : a ≠ 0 := by
      rintro rfl
      simp at hp
    refine Filter.Eventually.of_forall fun θ => ?_
    simpa using ha
  | succ n ih =>
    intro p hp
    have hq : MvPolynomial.finSuccEquiv ℂ n p ≠ 0 := by
      simpa using hp
    have hc := ih (MvPolynomial.finSuccEquiv ℂ n p).leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hq)
    have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => UnitAddCircle) 0
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => UnitAddCircle) 0 with he
    have hclosed : IsClosed {θ : Fin (n + 1) → UnitAddCircle |
        MvPolynomial.eval (fun i => (pt θ i : ℂ)) p = 0} :=
      isClosed_eq (continuous_eval_pt p) continuous_const
    have hm : MeasurableSet {z : UnitAddCircle × (Fin n → UnitAddCircle) |
        MvPolynomial.eval (fun i => (pt (e.symm z) i : ℂ)) p ≠ 0} :=
      e.symm.measurable hclosed.measurableSet.compl
    have hsymm : ∀ (s : UnitAddCircle) (θ : Fin n → UnitAddCircle),
        e.symm (s, θ) = (Fin.cons s θ : Fin (n + 1) → UnitAddCircle) := by
      intro s θ
      simp [he, MeasurableEquiv.piFinSuccAbove, Fin.insertNth_zero']
      rfl
    have hprod : ∀ᵐ z ∂(volume.prod volume : Measure (UnitAddCircle × (Fin n → UnitAddCircle))),
        MvPolynomial.eval (fun i => (pt (e.symm z) i : ℂ)) p ≠ 0 := by
      refine (Measure.ae_prod_iff_ae_ae hm).2 ?_
      refine (Measure.ae_ae_comm hm).2 ?_
      filter_upwards [hc] with θ' hθ'
      have hr : Polynomial.map (MvPolynomial.eval (fun i => (pt θ' i : ℂ)))
          (MvPolynomial.finSuccEquiv ℂ n p) ≠ 0 := by
        intro h
        apply hθ'
        rw [Polynomial.leadingCoeff, ← Polynomial.coeff_map, h, Polynomial.coeff_zero]
      refine ae_iff.2 (measure_mono_null ?_ (circle_zero_null _ hr))
      intro s hs
      have hs' : MvPolynomial.eval (fun i => (pt (e.symm (s, θ')) i : ℂ)) p = 0 := by
        by_contra h
        exact hs h
      rw [hsymm, eval_cons_pt] at hs'
      exact hs'
    have := hmp.quasiMeasurePreserving.ae hprod
    filter_upwards [this] with θ hθ
    rw [e.symm_apply_apply] at hθ
    exact hθ
