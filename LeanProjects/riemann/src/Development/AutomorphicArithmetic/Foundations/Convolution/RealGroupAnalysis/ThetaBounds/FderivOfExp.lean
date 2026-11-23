import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ExValCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.GrpEqMemArchCompact

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem fre_of_rays {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (u : V → ℂ) (G : V → V →L[ℝ] ℂ) (hG : Continuous G)
    (h : ∀ (X : V) (s : ℝ), HasDerivAt (fun s : ℝ => u (s • X)) (G (s • X) X) s) :
    HasFDerivAt u (G 0) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.1 hG.continuousAt c hc
  filter_upwards [Metric.ball_mem_nhds (0 : V) hδ] with X hX
  have hX' : ‖X‖ < δ := by simpa using hX
  have hv : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (fun s : ℝ => u (s • X) - (s : ℂ) * G 0 X)
      (G (s • X) X - G 0 X) (Set.Icc (0 : ℝ) 1) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * G 0 X) (G 0 X) s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (G 0 X)
    exact ((h X s).sub h1).hasDerivWithinAt
  have hbd : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖G (s • X) X - G 0 X‖ ≤ c * ‖X‖ := by
    intro s hs
    have hs' : ‖s • X‖ < δ := by
      rw [norm_smul, Real.norm_of_nonneg hs.1]
      calc s * ‖X‖ ≤ 1 * ‖X‖ := by gcongr; exact hs.2
        _ < δ := by simpa using hX'
    have h2 : ‖G (s • X) - G 0‖ < c := by
      simpa [dist_eq_norm] using hb (x := s • X) (by simpa [dist_eq_norm] using hs')
    calc ‖G (s • X) X - G 0 X‖ = ‖(G (s • X) - G 0) X‖ := by simp
      _ ≤ ‖G (s • X) - G 0‖ * ‖X‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ c * ‖X‖ := by gcongr
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hv hbd (convex_Icc 0 1)
    (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
  simp only [zero_smul, one_smul, Complex.ofReal_zero, Complex.ofReal_one, zero_mul, one_mul, sub_zero,
    norm_one, mul_one] at key
  have e : u (0 + X) - u 0 - G 0 X = u X - G 0 X - u 0 := by rw [zero_add]; ring
  rw [e]
  exact key

private theorem fderiv_of_exp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (f : V → ℂ) (ε : V → V) (L : V →L[ℝ] ℂ)
    (hε : HasStrictFDerivAt ε ((ContinuousLinearEquiv.refl ℝ V : V ≃L[ℝ] V) : V →L[ℝ] V) 0)
    (h : HasFDerivAt (f ∘ ε) L 0) : HasFDerivAt f L (ε 0) := by
  have hi := hε.to_localInverse
  have h0 := hε.localInverse_apply_image
  set l := HasStrictFDerivAt.localInverse ε _ 0 hε
  have h' : HasFDerivAt (f ∘ ε) L (l (ε 0)) := by rw [h0]; exact h
  have hc := h'.comp (ε 0) hi.hasFDerivAt
  have e : L.comp (((ContinuousLinearEquiv.refl ℝ V).symm : V ≃L[ℝ] V) : V →L[ℝ] V) = L := by
    ext x; simp
  rw [e] at hc
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [hε.eventually_right_inverse] with y hy
  simp only [Function.comp_apply]
  rw [hy]

section
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

private theorem exp_eq (Y : Lie E 2) : toL (NormedSpace.exp (Matrix.of Y)) =
    (Cm.archEq E 2).symm (NormedSpace.exp (Cm.archEq E 2 Y)) := by
  letI : NormedRing (Matrix (Fin 2) (Fin 2) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin 2) (Fin 2) (Cinf E)) := FiniteDimensional.complete ℝ _
  letI : NormedAlgebra ℚ (ArchMatrix E 2) := NormedAlgebra.restrictScalars ℚ ℝ _
  refine (Cm.archEq E 2).injective ?_
  rw [ContinuousLinearEquiv.apply_symm_apply, Cm.archEq_toL]
  have hc : Continuous (Cm.matEq E 2) := (Cm.archEq E 2).continuous
  exact NormedSpace.map_exp (Cm.matEq E 2) hc (Matrix.of Y)

private noncomputable def expL (Y : Lie E 2) : Lie E 2 := (Cm.archEq E 2).symm (NormedSpace.exp (Cm.archEq E 2 Y))

private theorem expL_strict : HasStrictFDerivAt (expL (E := E))
    ((ContinuousLinearEquiv.refl ℝ (Lie E 2) : Lie E 2 ≃L[ℝ] Lie E 2) : Lie E 2 →L[ℝ] Lie E 2) 0 := by
  have h1 : HasStrictFDerivAt (fun x : ArchMatrix E 2 => NormedSpace.exp x) (1 : ArchMatrix E 2 →L[ℝ] ArchMatrix E 2)
      (Cm.archEq E 2 0) := by
    rw [map_zero]; exact hasStrictFDerivAt_exp_zero
  have h2 := ((Cm.archEq E 2).symm.hasStrictFDerivAt.comp _ (h1.comp (0 : Lie E 2) (Cm.archEq E 2).hasStrictFDerivAt))
  refine h2.congr_fderiv (ContinuousLinearMap.ext fun x => ?_)
  exact (Cm.archEq E 2).symm_apply_apply x

private theorem expL_cont : Continuous (expL (E := E)) := by
  letI : NormedAlgebra ℚ (ArchMatrix E 2) := NormedAlgebra.restrictScalars ℚ ℝ _
  exact (Cm.archEq E 2).symm.continuous.comp (NormedSpace.exp_continuous.comp (Cm.archEq E 2).continuous)

private theorem toL_ex (Y : Lie E 2) : toL (ex Y 1).val = expL Y := by
  have : (ex Y 1).val = NormedSpace.exp (Matrix.of Y) := by
    rw [ex, IsUnit.unit_spec, one_smul]
  rw [this]
  exact exp_eq Y

private theorem ex_smul (X : Lie E 2) (s : ℝ) : ex (s • X) 1 = ex X s := by
  refine Units.ext ?_
  change NormedSpace.exp ((1 : ℝ) • Matrix.of (s • X)) = NormedSpace.exp (s • Matrix.of X)
  rw [one_smul]
  rfl

private theorem ex_zero (X : Lie E 2) : ex X 0 = 1 := by
  refine Units.ext ?_
  change NormedSpace.exp ((0 : ℝ) • Matrix.of X) = 1
  rw [zero_smul, NormedSpace.exp_zero]

private theorem ex_inv (X : Lie E 2) : (ex X 1)⁻¹ = ex (-X) 1 := by
  have h := (exPar E X).1 1 (-1)
  rw [add_neg_cancel, ex_zero] at h
  have e : ex (-X) 1 = ex X (-1) := by
    rw [← ex_smul X (-1), neg_one_smul]
  rw [e]
  exact inv_eq_of_mul_eq_one_right h.symm

private theorem ex_cont : Continuous fun Y : Lie E 2 => ex Y 1 := by
  have hv : Continuous fun Y : Lie E 2 => (ex Y 1).val := by
    have : (fun Y : Lie E 2 => (ex Y 1).val) = fun Y => Matrix.of (expL Y) := by
      funext Y; rw [← toL_ex]; rfl
    rw [this]
    exact expL_cont
  refine Units.continuous_iff.2 ⟨hv, ?_⟩
  have : (fun Y : Lie E 2 => ((ex Y 1)⁻¹).val) = fun Y => (ex (-Y) 1).val := by
    funext Y; rw [ex_inv]
  change Continuous (fun Y : Lie E 2 => ((ex Y 1)⁻¹).val)
  rw [this]
  exact hv.comp continuous_neg

end

theorem UpperTheory.ConvolutionTheory.R2.Ff.smFre :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], SmFre E := by
  intro E _ _ _ Φ T hc hd g
  let G : Lie E 2 → Lie E 2 →L[ℝ] ℂ := fun Y =>
    LinearMap.toContinuousLinearMap ((LinearMap.proj (g * infGL E 2 (ex Y 1))) ∘ₗ T)
  have hGa : ∀ Y X, G Y X = T X (g * infGL E 2 (ex Y 1)) := fun _ _ => rfl
  have hG : Continuous G := continuous_clm_apply.2 fun X => by
    simp only [hGa]
    exact (hc X g).comp ex_cont
  have hray : ∀ (X : Lie E 2) (s : ℝ), HasDerivAt (fun s : ℝ => Φ (g * infGL E 2 (ex (s • X) 1))) (G (s • X) X) s := by
    intro X s
    have h1 := hd X (g * infGL E 2 (ex X s))
    have h2 : HasDerivAt (fun r : ℝ => Φ (g * infGL E 2 (ex X s) * infGL E 2 (ex X (r - s))))
        (T X (g * infGL E 2 (ex X s))) s :=
      HasDerivAt.comp_sub_const s s (by simpa using h1)
    rw [hGa, ex_smul]
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)
    simp only [ex_smul]
    rw [mul_assoc, ← map_mul, ← (exPar E X).1, add_sub_cancel]
  have h1 := fre_of_rays (fun Y => Φ (g * infGL E 2 (ex Y 1))) G hG hray
  have h2 : HasFDerivAt (chart Φ g ∘ expL) (G 0) 0 := by
    refine h1.congr_of_eventuallyEq (Eventually.of_forall fun Y => ?_)
    simp only [Function.comp_apply]
    rw [← toL_ex, chart_val]
  have h3 := fderiv_of_exp (chart Φ g) expL (G 0) expL_strict h2
  have h0 : expL (0 : Lie E 2) = oneL E 2 := by
    rw [← toL_ex, ← zero_smul ℝ (0 : Lie E 2), ex_smul, ex_zero]
    rfl
  rw [h0] at h3
  refine ⟨h3.differentiableAt, fun X => ?_⟩
  rw [h3.fderiv, hGa, ← zero_smul ℝ (0 : Lie E 2), ex_smul, ex_zero, map_one, mul_one]
