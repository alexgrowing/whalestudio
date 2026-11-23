import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ParamDeriv
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

private theorem parametric_integral_deriv_bound (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (p : V)
    (O : Set (V × ℝ)) (hO : IsOpen O) (hp : ∀ t ∈ Set.Icc (0 : ℝ) 1, (p, t) ∈ O) (b : ℝ) (i : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (Φ : V × ℝ → F), ContDiffOn ℝ ∞ Φ O →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ i (fun x => Φ (x, t)) p‖ ≤ b) →
      ‖iteratedFDeriv ℝ i (fun x => ∫ t in (0 : ℝ)..1, Φ (x, t)) p‖ ≤ b := by
  induction i with
  | zero =>
    intro F _ _ _ Φ _ h
    simp only [norm_iteratedFDeriv_zero] at h ⊢
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := b) (f := fun t => Φ (p, t))
      (fun t ht => h t (by
        rw [Set.uIoc_of_le zero_le_one] at ht
        exact Set.Ioc_subset_Icc_self ht))
    simpa using this
  | succ i ih =>
    intro F _ _ _ Φ hΦ h
    let Ψ : V × ℝ → V →L[ℝ] F := fun z => (fderiv ℝ Φ z).comp (ContinuousLinearMap.inl ℝ V ℝ)
    have hΨ : ContDiffOn ℝ ∞ Ψ O :=
      (hΦ.fderiv_of_isOpen hO (by simp)).clm_comp contDiffOn_const
    have hd : ∀ x t, (x, t) ∈ O → fderiv ℝ (fun y => Φ (y, t)) x = Ψ (x, t) := fun x t hx => by
      have h1 : DifferentiableAt ℝ Φ (x, t) := (hΦ.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
      exact (h1.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x t)).fderiv
    have htube : ∀ᶠ x in 𝓝 p, ∀ t ∈ Set.Icc (0 : ℝ) 1, (x, t) ∈ O :=
      isCompact_Icc.eventually_forall_of_forall_eventually fun t ht => hO.mem_nhds (hp t ht)
    have e : fderiv ℝ (fun x => ∫ t in (0 : ℝ)..1, Φ (x, t)) =ᶠ[𝓝 p] fun x => ∫ t in (0 : ℝ)..1, Ψ (x, t) := by
      filter_upwards [htube] with x hx
      rw [(UpperTheory.V.Lit.Dr.paramDeriv V F x O Φ hO hx hΦ).2.fderiv]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le zero_le_one] at ht
      exact hd x t (hx t ht)
    rw [← norm_iteratedFDeriv_fderiv, (e.iteratedFDeriv ℝ i).eq_of_nhds]
    refine ih _ Ψ hΨ fun t ht => ?_
    have e' : fderiv ℝ (fun y => Φ (y, t)) =ᶠ[𝓝 p] fun x => Ψ (x, t) := by
      filter_upwards [htube] with x hx using hd x t (hx t ht)
    rw [← (e'.iteratedFDeriv ℝ i).eq_of_nhds, norm_iteratedFDeriv_fderiv]
    exact h t ht

theorem UpperTheory.V.Lit.Geo.Cs.intSz :
    IntSz := by
  intro V F _ _ _ _ _ _ k p O Φ b hO hp hΦ h i hi
  exact parametric_integral_deriv_bound V p O hO hp b i F Φ hΦ fun t ht => h t ht i hi
