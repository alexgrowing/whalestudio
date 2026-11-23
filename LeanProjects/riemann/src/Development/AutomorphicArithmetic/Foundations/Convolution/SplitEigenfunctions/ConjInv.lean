import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

def UU : Set (A ℚ)ˣ := {t | (t : A ℚ).1 = 1 ∧ ∀ v : H.P ℚ, Valued.v (H.cp v (t : A ℚ)) = 1}

structure UMeas where
  υ : Measure (IdeleGroup ℚ)
  prob : IsProbabilityMeasure υ
  supp : υ UUᶜ = 0
  inv : ∀ t ∈ UU, υ.map (fun x : IdeleGroup ℚ => (t * x : (A ℚ)ˣ)) = υ

variable {E : Type} [Field E] [NumberField E]

variable (E) in

def em : GL (Fin 2) (A ℚ) →* GL (Fin 2) (A E) := Matrix.GeneralLinearGroup.map (AdeleBaseChange.adeleMap ℚ E)

def Per (M : Meas ℚ) (U : UMeas) (χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) : ℂ :=
  ∫ t, ((χ.1 t : ℂˣ) : ℂ) * ∫ g in M.D, φ (em E (gl g * dM t)) ∂M.μ ∂U.υ

variable [IsTotallyComplex E]

def Tr (P : CuspSub E 2) : Submodule ℂ (GL (Fin 2) (A E) → ℂ) :=
  Submodule.span ℂ {φ | ∃ f ∈ P.V, ∃ h, φ = fun g => f.1 (g * h)}

def CenN (P : CuspSub E 2) (ω : HChar ℚ) : Prop :=
  ∀ f ∈ P.V, ∀ z g, f.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 (ideleNorm ℚ E z) : ℂˣ) : ℂ) * f.1 g

def ConjInv (P : CuspSub E 2) : Prop :=
  ∀ᶠ w : H.P E in cofinite, ∀ w' : H.P E, w'.under (𝓞 ℚ) = w.under (𝓞 ℚ) → ∃ B, (CG.mk P).HasSat w B ∧ (CG.mk P).HasSat w' B

def NoPer (M : Meas ℚ) (U : UMeas) (χ : HChar ℚ) (P : CuspSub E 2) : Prop :=
  ∀ f ∈ P.V, ∀ h, Per M U χ (fun g => f.1 (g * h)) = 0

def UMeasEx : Prop := Nonempty UMeas

def CenEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], Module.finrank ℚ E = 2 → ∀ P : CuspSub E 2, ConjInv P →
    ∃ ω : HChar ℚ, CenN P ω

def AsaiNV : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (_ : Dat ℚ E) (M : Meas ℚ) (U : UMeas) (P : CuspSub E 2) (ω η : HChar ℚ),
    ConjInv P → CenN P ω → (∀ a, ‖((ω.1 a : ℂˣ) : ℂ)‖ = 1) → IsQuadCharOf E η → ¬ (NoPer M U ω⁻¹ P ∧ NoPer M U (ω * η)⁻¹ P)

end UpperTheory.ConvolutionTheory.RankTwoDescent

end
