import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ActMat
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem cont_inf (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  have hs : Continuous (sInf E : Cinf E → Ad E) := (GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

private theorem cont_fin (E : Type) [Field E] [NumberField E] (a : ℕ) :
    Continuous (finGL E a) := by
  have hs : Continuous (sFin E : Af E → Ad E) := continuous_const.prodMk continuous_id
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

private theorem cont_unherm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (D : Dat F E) : Continuous D.unherm := by
  have hco : ∀ i, Continuous fun z => D.co z i := fun i => (continuous_apply i).comp D.continuous_co
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact (hco 0).comp (continuous_id.matrix_elem 1 1)
  · exact (hco 0).comp (continuous_id.matrix_elem 0 0)
  · exact (hco 0).comp (continuous_id.matrix_elem 0 1)
  · exact (hco 1).comp (continuous_id.matrix_elem 0 1)

private theorem cont_act {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (D : Dat F E) (v : V4 F) : Continuous fun h : GL (Fin 2) (A E) => D.act h v := by
  have hv : Continuous fun h : GL (Fin 2) (A E) => h.val := Units.continuous_val
  exact (cont_unherm D).comp ((hv.matrix_mul continuous_const).matrix_mul
    (hv.matrix_map D.continuous_bar).matrix_transpose)

theorem UpperTheory.ConvolutionTheory.R2.Ff.actCont :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E), ActCont D := by
  intro F E _ _ _ _ _ _ _ D
  obtain ⟨ρ, hρ, -, -⟩ := UpperTheory.ConvolutionTheory.R2.D.actMat F E D
  have hval : Continuous fun h => (ρ h).val := continuous_matrix fun i j => by
    have e : ∀ h, (ρ h).val i j = D.act h (Pi.single j 1) i := fun h => by rw [hρ]; simp
    simp only [e]
    exact (continuous_apply i).comp (cont_act D _)
  refine ⟨ρ, Units.continuous_iff.2 ⟨hval, ?_⟩, hρ, continuous_nu, cont_inf E 2, cont_fin E 2⟩
  have e : (fun h => (((ρ h)⁻¹ : GL (Fin 4) (A F)) : Matrix (Fin 4) (Fin 4) (A F))) = fun h => (ρ h⁻¹).val := by
    funext h; rw [map_inv]
  exact e ▸ hval.comp continuous_inv
