import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm
import GroundTheory.AutomorphicForms.QuotientMeasure

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.orbFn :
    OrbS → OrbFn := by
  intro hS E _ _ _ D M j hj c hc hcs
  have hstab := (hS E D).2.1
  haveI : PolishSpace (G1 E) := GroundTheory.Automorphic.polishSpace_of_locallyCompact
  haveI := M.haar
  haveI := M.right
  have hval : ∀ g : G1 ℚ, (j g).1 = g.1.map (AdeleBaseChange.adeleMap ℚ E) := fun g => by
    have := congrArg Units.val (hj g)
    simpa [em] using this
  have hjc : Continuous j := by
    refine continuous_induced_rng.2 ?_
    exact (continuous_subtype_val.matrix_map AdeleBaseChange.continuous_adeleMap).congr fun g => (hval g).symm
  set O : G1 E → V4 ℚ := fun h => D.act (gl h)⁻¹ (rp X0) with hO
  set cc : G1 E → ℂ := fun h => ∫ g, c (j g * h) ∂M.μ with hcc
  have hgl : Continuous fun h : G1 E => gl h := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    have e : ∀ h : G1 E, ((gl h)⁻¹ : GL (Fin 2) (A E)).val = (h⁻¹ : G1 E).1 := fun h => by
      have : (gl h)⁻¹ = gl h⁻¹ := by simp only [gl, map_inv]
      rw [this]; rfl
    have hi : Continuous fun h : G1 E => (h⁻¹ : G1 E).1 :=
      (continuous_subtype_val : Continuous fun g : G1 E => g.1).comp continuous_inv
    exact hi.congr fun h => (e h).symm
  have hglc : Continuous fun h : G1 E => (gl h)⁻¹ := hgl.inv
  have hOc : Continuous O := D.continuous_act' hglc continuous_const
  have hccm : Measurable cc := by
    have hF : StronglyMeasurable (Function.uncurry fun (h : G1 E) (g : G1 ℚ) => c (j g * h)) :=
      (hc.comp ((hjc.comp continuous_snd).mul continuous_fst)).stronglyMeasurable
    exact (hF.integral_prod_right (ν := M.μ)).measurable
  have hfac : Function.FactorsThrough cc O := by
    intro a b hab
    have h1 : D.act (gl (b * a⁻¹)) (rp X0) = rp X0 := by
      have hab' : D.act (gl a)⁻¹ (rp X0) = D.act (gl b)⁻¹ (rp X0) := hab
      have e : gl (b * a⁻¹) = gl b * (gl a)⁻¹ := by simp only [gl, map_mul, map_inv]
      rw [e, Dat.act_mul, hab', Dat.act_act_inv]
    obtain ⟨g0, hg0⟩ := (hstab (b * a⁻¹)).1 h1
    have h2 : b * a⁻¹ = j g0 := Matrix.SpecialLinearGroup.toGL_injective (hg0.trans (hj g0).symm)
    have h3 : b = j g0 * a := by rw [← h2]; group
    simp only [hcc]
    rw [h3]
    have := integral_mul_right_eq_self (μ := M.μ) (fun g => c (j g * a)) g0
    simp only [map_mul, mul_assoc] at this
    exact this.symm
  refine ⟨Function.extend O cc 0, ?_, fun h => hfac.extend_apply 0 h⟩
  have hR : MeasurableSet (Set.range O) := by
    obtain ⟨K, hK, hU⟩ := isSigmaCompact_range hOc
    rw [← hU]
    exact MeasurableSet.iUnion fun n => (hK n).measurableSet
  refine measurable_of_restrict_of_restrict_compl hR ?_ ?_
  · have hr : Measurable (Set.rangeFactorization O) := hOc.measurable.subtype_mk
    refine (Measurable.measurable_comp_iff_of_surjective hr Set.rangeFactorization_surjective).1 ?_
    have e : (Set.range O).domRestrict (Function.extend O cc 0) ∘ Set.rangeFactorization O = cc := by
      funext h
      exact hfac.extend_apply 0 h
    rw [e]
    exact hccm
  · have e : (Set.range O)ᶜ.domRestrict (Function.extend O cc 0) = fun _ => 0 := by
      funext x
      exact Function.extend_apply' cc (0 : V4 ℚ → ℂ) x.1 fun ⟨a, ha⟩ => x.2 ⟨a, ha⟩
    rw [e]
    exact measurable_const
