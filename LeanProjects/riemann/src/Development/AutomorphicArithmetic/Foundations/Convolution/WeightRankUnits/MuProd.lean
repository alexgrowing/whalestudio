import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.DeltaProdAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharFinprodLocKMulInfEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMInfinityComponentGlobalUnit

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem muAt_unit {E : Type} [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (u : Pl E) (k : Eˣ) :
    UpperTheory.ConvolutionTheory.G2.muAt μ u (k : E) = ((μ.locK u k : ℂˣ) : ℂ) := by
  have h : algebraMap E (u.adicCompletion E) (k : E) ≠ 0 := by
    simpa using k.ne_zero
  rw [UpperTheory.ConvolutionTheory.G2.muAt, dif_pos h, HChar.locK, MonoidHom.comp_apply]
  have hu : Units.mk0 (algebraMap E (u.adicCompletion E) (k : E)) h = atFin u k := Units.ext rfl
  rw [hu]

theorem UpperTheory.ConvolutionTheory.G2.muProd :
    UpperTheory.ConvolutionTheory.G2.MuProd := by
  intro E _ _ _ μ e hμ R hR
  obtain ⟨hf, hp⟩ := GlobalTheory.HCharUnit.finprod_locK_mul_inf E μ (Units.mk0 R hR)
  have hfun : (fun u : Pl E => UpperTheory.ConvolutionTheory.G2.muAt μ u R) =
      fun u : Pl E => (Units.coeHom ℂ) (μ.locK u (Units.mk0 R hR)) :=
    funext fun u => muAt_unit μ u (Units.mk0 R hR)
  have hsub : (Function.mulSupport fun u : Pl E => (Units.coeHom ℂ) (μ.locK u (Units.mk0 R hR))) ⊆
      Function.mulSupport fun u : Pl E => μ.locK u (Units.mk0 R hR) := by
    intro u hu h1
    exact hu (by simp only [h1, map_one])
  rw [hfun]
  refine ⟨hf.subset hsub, ?_⟩
  rw [← MonoidHom.map_finprod _ hf]
  have hinf := GlobalTheory.BCT.inf_mu_unit E μ e hμ (Units.mk0 R hR)
  simp only [Units.val_mk0] at hinf
  rw [← hinf]
  have := congrArg (Units.coeHom ℂ) hp
  simpa using this
