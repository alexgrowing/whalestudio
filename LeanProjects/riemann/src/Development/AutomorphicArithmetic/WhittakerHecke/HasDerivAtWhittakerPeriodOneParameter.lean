import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem cover : ∃ C : Set (Fin 2 → A ℚ), IsCompact C ∧ FS2 ℚ ⊆ C := by
  obtain ⟨C, hC, hEC⟩ : ∃ C, IsCompact C ∧ fundamentalSet ℚ ⊆ C :=
    ⟨closure (fundamentalSetInfinite ℚ) ×ˢ _,
      (isCompact_closure_fundamentalSetInfinite ℚ).prod (isCompact_integralFiniteAdeles ℚ),
      fun x hx => ⟨subset_closure hx.1, hx.2⟩⟩
  exact ⟨Set.univ.pi fun _ : Fin 2 => C, isCompact_univ_pi fun _ => hC, fun x hx i hi => hEC (hx i hi)⟩

private theorem cont_nE' {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) :
    Continuous fun u : Fin 2 → A ℚ => nE D u :=
  continuous_gl.comp (continuous_nU.comp ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 0)).add
    ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 1)).mul continuous_const)))

private theorem deriv_at {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (f : Sm E 2)
    (c : ℝ → GL (Fin 2) (Cinf E)) (X : Lie E 2) (x : GL (Fin 2) (A E)) (c0 : c 0 = 1)
    (cadd : ∀ s t, c (s + t) = c s * c t) (cd : HasDerivAt (fun t => toL (c t).val) X 0) (t : ℝ) :
    HasDerivAt (fun τ => f.1 (x * infGL E 2 (c τ))) ((lie E 2 X f).1 (x * infGL E 2 (c t))) t := by
  have h := hasDerivAt_curve f (x * infGL E 2 (c t)) c X c0 cd
  have h2 : HasDerivAt (fun s => f.1 (x * infGL E 2 (c t) * infGL E 2 (c s))) ((lie E 2 X f).1 (x * infGL E 2 (c t))) (t - t) := by
    rw [sub_self]; exact h
  have h3 := HasDerivAt.comp_sub_const t t h2
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun τ => ?_)
  have e : c τ = c t * c (τ - t) := by rw [← cadd]; congr 1; ring
  simp only [e, map_mul, mul_assoc]

theorem UpperTheory.hasDerivAt_whittakerPeriod_oneParameter :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (f : Sm E 2) (c : ℝ → GL (Fin 2) (Cinf E)) (X : Lie E 2)
        (g : GL (Fin 2) (A E)), c 0 = 1 → (∀ s t, c (s + t) = c s * c t) → HasDerivAt (fun t => toL (c t).val) X 0 →
        Continuous f.1 → Continuous (lie E 2 X f).1 → (∃ B : ℝ, ∀ g, ‖(lie E 2 X f).1 g‖ ≤ B) →
        HasDerivAt (fun t : ℝ => Wo D f.1 (g * infGL E 2 (c t))) (Wo D (lie E 2 X f).1 g) 0 := by
  intro E _ _ _ D f c X g c0 cadd cd hf hl ⟨B, hB⟩
  obtain ⟨C, hC, hsub⟩ := cover
  have hfin : adeleMeasurePi ℚ (FS2 ℚ) < ⊤ := (measure_mono hsub).trans_lt hC.measure_lt_top
  haveI : IsFiniteMeasure ((adeleMeasurePi ℚ).restrict (FS2 ℚ)) := ⟨by simpa using hfin⟩
  have hn := cont_nE' D
  have hψ : Continuous fun u : Fin 2 → A ℚ => ψ (u 1) := continuous_ψ.comp (continuous_apply 1)
  have hF : ∀ h : GL (Fin 2) (A E), Continuous fun u : Fin 2 → A ℚ => f.1 (nE D u * h) * ψ (u 1) :=
    fun h => (hf.comp (hn.mul continuous_const)).mul hψ
  have hF' : ∀ h : GL (Fin 2) (A E), Continuous fun u : Fin 2 → A ℚ => (lie E 2 X f).1 (nE D u * h) * ψ (u 1) :=
    fun h => (hl.comp (hn.mul continuous_const)).mul hψ
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (adeleMeasurePi ℚ).restrict (FS2 ℚ)) (x₀ := (0 : ℝ)) (s := Set.univ)
    (F := fun t u => f.1 (nE D u * (g * infGL E 2 (c t))) * ψ (u 1))
    (F' := fun t u => (lie E 2 X f).1 (nE D u * (g * infGL E 2 (c t))) * ψ (u 1))
    (bound := fun _ => B) Filter.univ_mem
    (Eventually.of_forall fun t => (hF _).aestronglyMeasurable)
    (((hF _).continuousOn.integrableOn_compact hC).mono_set hsub)
    (hF' _).aestronglyMeasurable
    (ae_of_all _ fun u t _ => by rw [norm_mul, norm_ψ, mul_one]; exact hB _)
    (integrable_const _)
    (ae_of_all _ fun u t _ => by
      have h := deriv_at f c X (nE D u * g) c0 cadd cd t
      simp only [mul_assoc] at h
      exact h.mul_const (ψ (u 1)))
  have h2 := key.2
  simp only [c0, map_one, mul_one] at h2
  exact h2
