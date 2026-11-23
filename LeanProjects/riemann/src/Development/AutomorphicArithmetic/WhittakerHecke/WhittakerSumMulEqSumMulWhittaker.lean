import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.XgDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.NormWfLe
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.whittaker_sum_mul_eq_sum_mul_whittaker :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ι : Type) (s : Finset ι) (c : ι → ℂ) (φ : ι → GL (Fin 2) (A E) → ℂ), (∀ i, Continuous (φ i)) → (∀ i, ∃ B : ℝ, ∀ g, ‖φ i g‖ ≤ B) → ∀ h : GL (Fin 2) (A E), Wo D (fun g => ∑ i ∈ s, c i * φ i g) h = ∑ i ∈ s, c i * Wo D (φ i) h := by
  intro E _ _ D ι s c φ hc hb h
  haveI : IsFiniteMeasure ((adeleMeasurePi (ι := Fin 2) ℚ).restrict (FS2 ℚ)) := ⟨by
    rw [Measure.restrict_apply_univ]
    have h1 : adeleMeasurePi (ι := Fin 2) ℚ (FS2 ℚ) = 1 :=
      GroundTheory.Automorphic.FourierWhittaker.vecMeasure_vecDomain
    rw [h1]
    exact ENNReal.one_lt_top⟩
  have hψ : Continuous (ψ (F := ℚ)) := continuous_subtype_val.comp continuous_adelicChar
  have hn : Continuous (nE D : (Fin 2 → A ℚ) → GL (Fin 2) (A E)) :=
    UpperTheory.ConvolutionTheory.R2.Pp.cont_n.comp (D.continuous_mkE' (continuous_apply 0) (continuous_apply 1))
  have hi : ∀ i, Integrable (fun u : Fin 2 → A ℚ => φ i (nE D u * h) * ψ (u 1))
      ((adeleMeasurePi (ι := Fin 2) ℚ).restrict (FS2 ℚ)) := by
    intro i
    obtain ⟨B, hB⟩ := hb i
    refine Integrable.of_bound (C := B)
      (((hc i).comp (hn.mul continuous_const)).mul
        (hψ.comp (continuous_apply 1))).aestronglyMeasurable ?_
    refine ae_of_all _ fun u => ?_
    rw [norm_mul, show ‖ψ (u 1)‖ = 1 from Circle.norm_coe _, mul_one]
    exact hB _
  have e : ∀ u : Fin 2 → A ℚ, (∑ i ∈ s, c i * φ i (nE D u * h)) * ψ (u 1) =
      ∑ i ∈ s, c i * (φ i (nE D u * h) * ψ (u 1)) := fun u => by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
  simp only [Wo, e]
  rw [integral_finset_sum _ fun i _ => (hi i).const_mul (c i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
