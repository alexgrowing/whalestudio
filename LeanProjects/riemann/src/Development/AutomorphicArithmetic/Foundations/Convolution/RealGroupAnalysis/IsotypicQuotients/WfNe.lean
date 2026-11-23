import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.InfDec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.CuspZero
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FoundBridge
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

theorem UpperTheory.ConvolutionTheory.R2.Pp.wfNe :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], UpperTheory.ConvolutionTheory.R2.Pp.WfNe F := by
  intro F _ _ _ π
  obtain ⟨f, hf, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  obtain ⟨ω, -, hω⟩ := UpperTheory.ConvolutionTheory.R2.cen F π
  obtain ⟨x, hx⟩ : ∃ x, Wf f.1 x ≠ 0 := by
    by_contra hn
    push Not at hn
    obtain ⟨φ, rfl⟩ := Fb.mem_range_ofCusp.2 (π.cusp f hf)
    exact h0 (Subtype.ext (eq_zero_of_Wf φ.2 (cuspZero F π _ hf).1 hn))
  obtain ⟨g, s, k, y, hg, rfl⟩ := infDec F x
  refine ⟨TR.act (.cpt k) (TR.act (.fin y) f), π.stable _ _ (π.stable _ _ hf), g, hg, fun h => hx ?_⟩
  unfold Wf at h ⊢
  rw [← mul_zero ((ω s : ℂˣ) : ℂ), ← h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  have e : ∀ z : GL (Fin 2) (A F), gl (nU b) * (Matrix.GeneralLinearGroup.scalar (Fin 2) s * z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) s * (gl (nU b) * z) := fun z => by
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    exact Units.ext ((Matrix.scalar_commute (s : A F) (fun _ => mul_comm _ _) _).eq.symm)
  simp only
  rw [e, hω f hf, mul_assoc, ← mul_assoc (gl (nU b)), ← mul_assoc (gl (nU b))]
  rfl
