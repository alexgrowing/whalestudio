import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SExpDefs
import GroundTheory.GlobalFields.TateThesis.EulerFactorsInfinite
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published
open NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L5

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

variable (F) in

def wpoly (x : mixedSpace F) : ℂ :=
  ∏ v : InfinitePlace F, (1 + ((x.1 ⟨v, IsTotallyReal.isReal v⟩ : ℝ) : ℂ) ^ 2)

variable (F) in

def phi1 : 𝓢(mixedSpace F, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (wpoly F)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclidean F)
      (gaussianSchwartz (euclidean.mixedSpace F)))

variable (F) in

def H1 : Ad F → ℂ := schwartzBruhatTensor (phi1 F) (cosetIndicator 1 0)

def condZ (c : HeightOneSpectrum (𝓞 F) → ℕ) (Z : Ad F) : Prop :=
  ∀ w, Valued.v (pLoc F w (pFin F Z)) ≤ WithZero.exp ((c w : ℤ) + dd w)

def theta (G : Ad F → ℂ) (b : IdeleGroup F) : ℝ := ∑' ξ : Fˣ, ‖G (b • algebraMap F (Ad F) (ξ : F))‖

def gB (t : {r : ℝ // 0 < r}) : ℝ := if 1 ≤ (t : ℝ) then (t : ℝ)⁻¹ else (t : ℝ)

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L5

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open L5

def P5dom : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F],
  H1 F ∈ schwartzBruhat F ∧ (∀ x : Ad F, H1 F x = ((‖H1 F x‖ : ℝ) : ℂ)) ∧
    ∀ (c : HeightOneSpectrum (𝓞 F) → ℕ) (A Z Z' : Ad F), Z'.1 = Z.1 →
      (condZ c Z → Z'.2 ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)) →
      ‖kernF c A Z‖ ≤ ‖H1 F A‖ * ‖H1 F Z'‖

def P5mu : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (c : HeightOneSpectrum (𝓞 F) → ℕ),
  {w | c w ≠ 0}.Finite → ∃ μ : IdeleGroup F, (∀ Z : Ad F, (μ • Z).1 = Z.1) ∧
    ∀ Z : Ad F, condZ c Z → (μ • Z).2 ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)

def P5meas : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (c : HeightOneSpectrum (𝓞 F) → ℕ) (κ : ℂ),
  (∀ A Z : Ad F, adelicFourier F (slice c A) Z = κ * kernF c A Z) → ∀ (Y : Ad F) (ξ : F),
    Measurable fun p : {r : ℝ // 0 < r} × normOneSubgroup F => coefK c Y (tau p.1 p.2) ξ

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
