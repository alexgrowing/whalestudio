import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.NormWfLe
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

theorem UpperTheory.ConvolutionTheory.R2.Pp.wfBasic :
    ∀ (F : Type) [Field F] [NumberField F], UpperTheory.ConvolutionTheory.R2.Pp.WfBasic F := by
  intro F _ _ f hf
  have hc : ∀ {f : GL (Fin 2) (A F) → ℂ}, Lf f → ∀ g, IntegrableOn (fun b => f (gl (nU b) * g) * ψ b) (fundamentalSet F)
      (adeleMeasure F) := fun hf g => intOn ((hf.1.comp (cont_n.mul continuous_const)).mul cont_ψ)
  refine ⟨?_, fun b g => ?_, hc hf, fun c g => ?_, fun f' hf' g => ?_⟩
  · obtain ⟨C, hC, hs⟩ := exists_cpt (F := F)
    have e : Wf f = fun g => ∫ b in C, f (gl (nU b) * g) * ψ b ∂((adeleMeasure F).restrict (fundamentalSet F)) := by
      funext g
      rw [Measure.restrict_restrict hC.measurableSet, Set.inter_eq_right.2 hs]; rfl
    rw [e]
    haveI : IsFiniteMeasure ((adeleMeasure F).restrict (fundamentalSet F)) :=
      isFiniteMeasure_restrict.2 (by rw [adeleMeasure_fundamentalSet]; exact ENNReal.one_ne_top)
    exact continuous_parametric_integral_of_continuous
      ((hf.1.comp ((cont_n.comp continuous_snd).mul continuous_fst)).mul (cont_ψ.comp continuous_snd)) hC
  · unfold Wf
    rw [← integral_const_mul, ← int_add (h := fun x => ψ (-b) * (f (gl (nU x) * g) * ψ x))
      (fun k x => by rw [hf.per, ψ_add, ψ_rt, one_mul]) b]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have : ψ (-b) * ψ (x + b) = ψ x := by rw [← ψ_add]; congr 1; ring
    simp only [n_add, mul_assoc]
    rw [mul_left_comm, this]
  · unfold Wf
    rw [← integral_const_mul]
    simp [mul_assoc]
  · unfold Wf
    rw [← integral_add (hc hf g) (hc hf' g)]
    simp [add_mul]
