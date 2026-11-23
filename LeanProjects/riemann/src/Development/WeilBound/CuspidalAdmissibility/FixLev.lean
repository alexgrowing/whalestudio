import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OfinProd

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.RightCosetSpace
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C
open scoped RestrictedProduct Classical

namespace PositivityTheory.TfC.FixLev

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem finAt_finEmb (u : AdelicGLn.FiniteAdelicGL K n) (v : Pl K) :
    finAt v (finEmb K n u) =
      (AdelicGLn.finiteRestrictedEquiv K n u v : GL (Fin n) (v.adicCompletion K)) := by
  ext a b
  rw [finAt_apply, AdelicGLn.finiteRestrictedEquiv_apply, ← AdelicGLn.prodEquiv_apply_snd,
    prodEquiv_finEmb]

section Rep

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

theorem rhoF_mul (a b : AdelicGLn.FiniteAdelicGL K n) (x : LL μ) :
    rhoF μ (a * b) x = rhoF μ a (rhoF μ b x) := by
  simp only [rhoF, map_mul]
  exact UnitaryRep.map_mul_apply _ _ _ _

theorem rhoF_one (x : LL μ) : rhoF μ 1 x = x := by
  simp only [rhoF, map_one]
  exact UnitaryRep.map_one_apply _ _

def stab (x : LL μ) : Subgroup (AdelicGLn.FiniteAdelicGL K n) where
  carrier := {g | rhoF μ g x = x}
  one_mem' := rhoF_one μ x
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [rhoF_mul, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    calc rhoF μ a⁻¹ x = rhoF μ a⁻¹ (rhoF μ a x) := by rw [ha]
      _ = x := by rw [← rhoF_mul, inv_mul_cancel, rhoF_one]

end Rep

end PositivityTheory.TfC.FixLev
