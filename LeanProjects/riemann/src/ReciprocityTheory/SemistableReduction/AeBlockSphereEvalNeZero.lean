import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric

theorem ae_eval_ne_zero_of_ne_zero_fin : ∀ (m : ℕ) (f : MvPolynomial (Fin m) ℂ), f ≠ 0 →
    ∀ᵐ x ∂(volume : Measure (Fin m → ℂ)), MvPolynomial.eval x f ≠ 0 := by
  intro m
  induction m with
  | zero =>
    intro f hf
    refine Filter.Eventually.of_forall fun x => ?_
    rw [MvPolynomial.eq_C_of_isEmpty f] at hf ⊢
    simpa using hf
  | succ m ih =>
    intro f hf
    set P := MvPolynomial.finSuccEquiv ℂ m f with hPdef
    have hP : P ≠ 0 := by
      intro h
      apply hf
      exact (MvPolynomial.finSuccEquiv ℂ m).injective (by rw [← hPdef, h, map_zero])
    obtain ⟨k, hk⟩ : ∃ k, P.coeff k ≠ 0 := by
      by_contra h
      push Not at h
      exact hP (Polynomial.ext fun k => by simpa using h k)
    have h1 := ih _ hk
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) 0
    have he : MeasurePreserving e volume volume := volume_preserving_piFinSuccAbove _ 0
    have hmeas : MeasurableSet {z : ℂ × (Fin m → ℂ) | MvPolynomial.eval (e.symm z) f ≠ 0} :=
      ((MvPolynomial.continuous_eval f).measurable.comp e.symm.measurable)
        (measurableSet_singleton 0).compl
    have key : ∀ᵐ z ∂(volume : Measure (ℂ × (Fin m → ℂ))), MvPolynomial.eval (e.symm z) f ≠ 0 := by
      rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hmeas]
      rw [Measure.ae_ae_comm (p := fun y s => MvPolynomial.eval (e.symm (y, s)) f ≠ 0) hmeas]
      filter_upwards [h1] with s hs
      have hQ : Polynomial.map (MvPolynomial.eval s) P ≠ 0 := by
        intro h
        apply hs
        have := congrArg (fun q => Polynomial.coeff q k) h
        simpa [Polynomial.coeff_map] using this
      have hfin : ({y : ℂ | Polynomial.eval y (Polynomial.map (MvPolynomial.eval s) P) = 0}).Finite :=
        Polynomial.finite_setOfPred_isRoot hQ
      have hnull := hfin.measure_zero (volume : Measure ℂ)
      rw [measure_eq_zero_iff_ae_notMem] at hnull
      filter_upwards [hnull] with y hy
      have hc : (e.symm (y, s) : Fin (m + 1) → ℂ) = Fin.cons y s := by
        simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]; rfl
      rw [hc, MvPolynomial.eval_eq_eval_mv_eval']
      exact hy
    have := he.quasiMeasurePreserving.ae key
    filter_upwards [this] with x hx
    simpa using hx

theorem ae_eval_ne_zero_linear {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] {ι : Type*} [Fintype ι] (L : V ≃ₗ[ℂ] (ι → ℂ))
    (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    ∀ᵐ x ∂μ, MvPolynomial.eval (L x) f ≠ 0 := by
  set e := Fintype.equivFin ι
  set g := MvPolynomial.rename e f
  have hg : g ≠ 0 := by
    intro h
    apply hf
    exact MvPolynomial.rename_injective _ e.injective (by rw [map_zero]; exact h)
  set L' : V ≃ₗ[ℂ] (Fin (Fintype.card ι) → ℂ) := L.trans (LinearEquiv.funCongrLeft ℂ ℂ e.symm)
  have hL' : ∀ x, MvPolynomial.eval (L' x) g = MvPolynomial.eval (L x) f := by
    intro x
    have hc : (L' x : Fin (Fintype.card ι) → ℂ) ∘ e = L x := by
      funext i
      simp [L', LinearEquiv.funCongrLeft_apply]
    simp only [g, MvPolynomial.eval_rename, hc]
  have hac : μ.map L' ≪ volume := Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have h1 : ∀ᵐ y ∂(μ.map L'), MvPolynomial.eval y g ≠ 0 :=
    hac.ae_le (ae_eval_ne_zero_of_ne_zero_fin _ g hg)
  have hmeasL : Measurable L' := L'.toContinuousLinearEquiv.continuous.measurable
  have hmeasS : MeasurableSet {y : Fin (Fintype.card ι) → ℂ | MvPolynomial.eval y g ≠ 0} :=
    (MvPolynomial.continuous_eval g).measurable (measurableSet_singleton 0).compl
  rw [ae_map_iff hmeasL.aemeasurable hmeasS] at h1
  filter_upwards [h1] with x hx
  rwa [← hL']

theorem eval_blockScale_eq_prod_pow_mul {B n : ℕ} (a : Fin B → ℕ) (F : MvPolynomial (Fin B × Fin n) ℂ)
    (hF : IsMultiHomogeneous a F) (r : Fin B → ℂ) (x : Fin B × Fin n → ℂ) :
    MvPolynomial.eval (fun p => r p.1 * x p) F = (∏ b, r b ^ a b) * MvPolynomial.eval x F := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h1 : ∏ p, (r p.1 * x p) ^ s p = (∏ b, r b ^ a b) * ∏ p, x p ^ s p := by
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun b _ => ?_
    show ∏ j, r b ^ s (b, j) = r b ^ a b
    rw [Finset.prod_pow_eq_pow_sum, hF s hs b]
  rw [h1]
  ring

def blockCoordEquiv (B n : ℕ) : (Fin B → EuclideanSpace ℂ (Fin n)) ≃ₗ[ℂ] (Fin B × Fin n → ℂ) :=
  (LinearEquiv.piCongrRight fun _ => WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).trans
    (LinearEquiv.curry ℂ ℂ (Fin B) (Fin n)).symm

theorem blockCoordEquiv_apply {B n : ℕ} (y : Fin B → EuclideanSpace ℂ (Fin n)) (p : Fin B × Fin n) :
    blockCoordEquiv B n y p = WithLp.ofLp (y p.1) p.2 := rfl

theorem ae_toSphere (B n : ℕ) (a : Fin B → ℕ) (F : MvPolynomial (Fin B × Fin n) ℂ)
    (hF0 : F ≠ 0) (hF : IsMultiHomogeneous a F) :
    ∀ᵐ z ∂(Measure.pi fun _ : Fin B => (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere),
      MvPolynomial.eval (blockPoint z) F ≠ 0 := by
  set E := EuclideanSpace ℂ (Fin n)
  set νS := (volume : Measure E).toSphere
  set ρ := Measure.volumeIoiPow (Module.finrank ℝ E - 1)
  set Z : Set (Fin B → sphere (0 : E) 1) := {z | MvPolynomial.eval (blockPoint z) F = 0}
  have hZ : MeasurableSet Z := by
    have : Continuous fun z : Fin B → sphere (0 : E) 1 => MvPolynomial.eval (blockPoint z) F := by
      refine (MvPolynomial.continuous_eval F).comp ?_
      refine continuous_pi fun p => ?_
      unfold blockPoint spherePoint
      fun_prop
    exact this.measurable (measurableSet_singleton 0)
  have : (Measure.pi fun _ : Fin B => (volume : Measure E)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have : IsFiniteMeasure νS := by show IsFiniteMeasure ((volume : Measure E).toSphere); infer_instance
  have : SigmaFinite ρ := by show SigmaFinite (Measure.volumeIoiPow (Module.finrank ℝ E - 1)); infer_instance
  have hlin : ∀ᵐ y ∂(Measure.pi fun _ : Fin B => (volume : Measure E)),
      MvPolynomial.eval (blockCoordEquiv B n y) F ≠ 0 :=
    ae_eval_ne_zero_linear _ (blockCoordEquiv B n) F hF0
  set S : Set (Fin B → E) := {y | MvPolynomial.eval (blockCoordEquiv B n y) F = 0}
  have hS0 : (Measure.pi fun _ : Fin B => (volume : Measure E)) S = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hlin] with y hy
    exact hy
  have hSm : MeasurableSet S := by
    have : Continuous fun y : Fin B → E => MvPolynomial.eval (blockCoordEquiv B n y) F := by
      refine (MvPolynomial.continuous_eval F).comp ?_
      exact (blockCoordEquiv B n).toContinuousLinearEquiv.continuous
    exact this.measurable (measurableSet_singleton 0)
  have h1 := Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure E)
  have hprodSF : SigmaFinite (νS.prod ρ) := inferInstance
  have hT := measurePreserving_pi (hν := fun _ => hprodSF)
    (fun _ : Fin B => (volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E))
    (fun _ => νS.prod ρ) (fun _ => h1)
  have hA := measurePreserving_arrowProdEquivProdArrow (sphere (0 : E) 1) (Set.Ioi (0 : ℝ)) (Fin B)
    (fun _ => νS) (fun _ => ρ)
  set A := MeasurableEquiv.arrowProdEquivProdArrow (sphere (0 : E) 1) (Set.Ioi (0 : ℝ)) (Fin B)
  set T : (Fin B → ({0}ᶜ : Set E)) → (Fin B → sphere (0 : E) 1 × Set.Ioi (0 : ℝ)) :=
    fun x b => homeomorphUnitSphereProd E (x b)
  have hW : MeasurableSet (Z ×ˢ (Set.univ : Set (Fin B → Set.Ioi (0 : ℝ)))) :=
    hZ.prod MeasurableSet.univ
  have hAW : MeasurableSet (A ⁻¹' (Z ×ˢ Set.univ)) := A.measurable hW
  have e1 := Measure.prod_prod (μ := Measure.pi fun _ : Fin B => νS)
    (ν := Measure.pi fun _ : Fin B => ρ) Z Set.univ
  rw [← hA.measure_preimage hW.nullMeasurableSet, ← hT.measure_preimage hAW.nullMeasurableSet] at e1
  set G : (Fin B → ({0}ᶜ : Set E)) → (Fin B → E) := fun x b => (x b : E)
  have hsub : T ⁻¹' (A ⁻¹' (Z ×ˢ Set.univ)) ⊆ G ⁻¹' S := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true] at hx
    have hx' : MvPolynomial.eval (blockPoint fun b => (homeomorphUnitSphereProd E (x b)).1) F = 0 := by
      simpa [A, T, Z, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow] using hx
    have hcoord : blockCoordEquiv B n (G x) = fun p => ((‖(x p.1 : E)‖ : ℝ) : ℂ) *
        blockPoint (fun b => (homeomorphUnitSphereProd E (x b)).1) p := by
      funext p
      have hne : ‖(x p.1 : E)‖ ≠ 0 := norm_ne_zero_iff.2 (x p.1).2
      simp only [blockCoordEquiv_apply, G, blockPoint, spherePoint, homeomorphUnitSphereProd_apply_fst_coe]
      rw [← Complex.coe_smul, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc,
        ← Complex.ofReal_mul, mul_inv_cancel₀ hne, Complex.ofReal_one, one_mul]
    show MvPolynomial.eval (blockCoordEquiv B n (G x)) F = 0
    have hsc := eval_blockScale_eq_prod_pow_mul a F hF (fun b => ((‖(x b : E)‖ : ℝ) : ℂ))
      (blockPoint (fun b => (homeomorphUnitSphereProd E (x b)).1))
    rw [hcoord, hsc, hx', mul_zero]
  have hmap : ∀ _ : Fin B, ((volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E)).map
      Subtype.val = (volume : Measure E).restrict {0}ᶜ :=
    fun _ => map_comap_subtype_coe (measurableSet_singleton 0).compl _
  have hmSF : ∀ i : Fin B, SigmaFinite
      (((volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E)).map Subtype.val) := by
    intro i; rw [hmap i]; infer_instance
  have hG : (Measure.pi fun _ : Fin B =>
      (volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E)).map G =
      Measure.pi fun _ : Fin B => (volume : Measure E).restrict {0}ᶜ := by
    rw [Measure.pi_map_pi (hμ := hmSF) (fun _ => measurable_subtype_coe.aemeasurable)]
    exact congrArg _ (funext hmap)
  have hGm : Measurable G := measurable_pi_lambda _ fun b => measurable_subtype_coe.comp
    (measurable_pi_apply b)
  have hzero : (Measure.pi fun _ : Fin B =>
      (volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E))
      (T ⁻¹' (A ⁻¹' (Z ×ˢ Set.univ))) = 0 := by
    refine measure_mono_null hsub ?_
    rw [← Measure.map_apply hGm hSm, hG, ← Measure.restrict_pi_pi]
    exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans hS0.le)
  have hρ : ρ Set.univ ≠ 0 := by
    intro h
    have h2 := measure_mono_null (Set.subset_univ (Set.Iio (⟨1, by norm_num⟩ : Set.Ioi (0 : ℝ)))) h
    have h3 := Measure.volumeIoiPow_apply_Iio (Module.finrank ℝ E - 1) ⟨1, by norm_num⟩
    rw [show ρ (Set.Iio ⟨1, by norm_num⟩) = _ from h3] at h2
    rw [ENNReal.ofReal_eq_zero] at h2
    have h4 : (0 : ℝ) < (1 : ℝ) ^ (Module.finrank ℝ E - 1 + 1) / ((Module.finrank ℝ E - 1 : ℕ) + 1) := by
      positivity
    exact absurd h2 (not_le.2 h4)
  have hpiρ : (Measure.pi fun _ : Fin B => ρ) Set.univ ≠ 0 := by
    rw [Measure.pi_univ]
    exact Finset.prod_ne_zero_iff.2 fun _ _ => hρ
  rw [hzero] at e1
  have hZ0 : (Measure.pi fun _ : Fin B => νS) Z = 0 := by
    rcases mul_eq_zero.1 e1.symm with h | h
    · exact h
    · exact absurd h hpiρ
  rw [measure_eq_zero_iff_ae_notMem] at hZ0
  filter_upwards [hZ0] with z hz
  exact hz

theorem blockSphereMeasure_eq (B n : ℕ) :
    blockSphereProb B n = ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ)⁻¹ ^ B •
      Measure.pi fun _ : Fin B => (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by
  unfold blockSphereProb
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  simp only [sphereProb, ProbabilityTheory.cond_apply MeasurableSet.univ, Set.univ_inter,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem ae_blockSphere_eval_ne_zero (B n : ℕ) (a : Fin B → ℕ) (F : MvPolynomial (Fin B × Fin n) ℂ)
    (hF0 : F ≠ 0) (hF : IsMultiHomogeneous a F) :
    ∀ᵐ z ∂(blockSphereProb B n), MvPolynomial.eval (blockPoint z) F ≠ 0 := by
  rw [blockSphereMeasure_eq]
  exact Measure.ae_smul_measure (ae_toSphere B n a F hF0 hF) _

end ReciprocityTheory.MultiplicativeHeights
