import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
import GroundTheory.GlobalFields.TateThesis.AdelePoisson
import GroundTheory.GlobalFields.TateThesis.TateThetaDecay

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def gPt (x : UpperTheory.V.TR.Rinf F) (y : (UpperTheory.V.TR.Rinf F)ˣ) (yf : (Af F)ˣ) : GA F 2 :=
  UpperTheory.V.TR.infGL F 2 (aff y x) * finGL F 2 (aff yf 0)

def yAd (y : (UpperTheory.V.TR.Rinf F)ˣ) (yf : (Af F)ˣ) : Ad F :=
  ((UpperTheory.V.TR.infId F y * finId F yf : (Ad F)ˣ) : Ad F)

def tau (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) : IdeleGroup F :=
  moduleSection (w0 F) t * (u : IdeleGroup F)

def wt (ω : HChar F) (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) : ℂ :=
  ((ω.1 (tau t u) : ℂˣ) : ℂ)⁻¹ * ((t : ℝ) : ℂ)

variable (F) in

abbrev muE : Measure ({r : ℝ // 0 < r} × normOneSubgroup F) :=
  posRealMeasure.prod ((normOneMeasure F).restrict (normOneFundamentalDomain F))

def zeroRow (c : HeightOneSpectrum (𝓞 F) → ℕ) (τ : IdeleGroup F) : ℂ :=
  ∑' b : Fˣ, Phi c ![0, (τ : Ad F) * algebraMap F (Ad F) (b : F)]

def slice (c : HeightOneSpectrum (𝓞 F) → ℕ) (A : Ad F) (B : Ad F) : ℂ := Phi c ![A, B]

def kern (c : HeightOneSpectrum (𝓞 F) → ℕ) (Y : Ad F) (τ : IdeleGroup F) (ξ : F) : ℂ :=
  ((ideleModule F τ : ℝ)⁻¹ : ℂ) *
    adelicFourier F (slice c ((τ : Ad F) * Y)) (τ⁻¹ • algebraMap F (Ad F) ξ)

def coefK (c : HeightOneSpectrum (𝓞 F) → ℕ) (Y : Ad F) (τ : IdeleGroup F) (ξ : F) : ℂ :=
  ∑' a : Fˣ, kern c Y (τ * diagonal F a) ξ

def ex (ξ : F) (x : UpperTheory.V.TR.Rinf F) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v ξ : ℂ) * (x v : ℂ))

open Classical in

def kernF (c : HeightOneSpectrum (𝓞 F) → ℕ) (A Z : Ad F) : ℂ :=
  (∏ v, (((UpperTheory.V.TR.pInf F A v : ℂ) + (UpperTheory.V.TR.pInf F Z v : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * ((UpperTheory.V.TR.pInf F A v : ℂ) ^ 2 + (UpperTheory.V.TR.pInf F Z v : ℂ) ^ 2)))) *
    if (∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ))) ∧
        (∀ w, Valued.v (pLoc F w (pFin F Z)) ≤ WithZero.exp ((c w : ℤ) + dd w))
    then ((finiteAdelicChar F (pFin F Z) : Circle) : ℂ) else 0

def divS (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (𝔪 : Ideal (𝓞 F)) : ℂ :=
  ∑ᶠ 𝔯 ∈ {𝔯 | 𝔯 ∣ 𝔪}, chiI ω c 𝔯

def SKern : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (c : HeightOneSpectrum (𝓞 F) → ℕ),
  {w | c w ≠ 0}.Finite → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ A Z : Ad F, adelicFourier F (slice c A) Z = κ * kernF c A Z

def SFin : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → {w | c w ≠ 0}.Finite

def SZero : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → Integrable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F => zeroRow c (tau p.1 p.2) * wt ω p.1 p.2) (muE F)

def SPoint : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∀ (x : UpperTheory.V.TR.Rinf F) (y : (UpperTheory.V.TR.Rinf F)ˣ), (∀ v, 0 < y.val v) → ∀ (yf : (Af F)ˣ) (τ : IdeleGroup F),
    thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) τ * gPt x y yf) =
      zeroRow c τ + coefK c (yAd y yf) τ 0 + ∑' ξ : Fˣ, ex (ξ : F) x * coefK c (yAd y yf) τ ξ

def SNull : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∀ (y : (UpperTheory.V.TR.Rinf F)ˣ) (yf : (Af F)ˣ) (t : {r : ℝ // 0 < r}),
    IntegrableOn (fun u => coefK c (yAd y yf) (tau t u) 0 * ((ω.1 (tau t u) : ℂˣ) : ℂ)⁻¹) (normOneFundamentalDomain F)
      (normOneMeasure F) →
    ∫ u in normOneFundamentalDomain F, coefK c (yAd y yf) (tau t u) 0 * ((ω.1 (tau t u) : ℂˣ) : ℂ)⁻¹ ∂normOneMeasure F = 0

def SAbs : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∀ (y : (UpperTheory.V.TR.Rinf F)ˣ), (∀ v, 0 < y.val v) → ∀ yf : (Af F)ˣ,
    (∀ ξ : F, AEStronglyMeasurable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F => coefK c (yAd y yf) (tau p.1 p.2) ξ) (muE F)) ∧
    (∀ p : {r : ℝ // 0 < r} × normOneSubgroup F, Summable fun ξ : Fˣ => ‖coefK c (yAd y yf) (tau p.1 p.2) ξ‖) ∧
    Integrable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
      (∑' ξ : Fˣ, ‖coefK c (yAd y yf) (tau p.1 p.2) ξ‖) * (p.1 : ℝ)) (muE F)

def SUnfold : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∀ (Y : Ad F) (ξ : F),
    Integrable (fun τ : IdeleGroup F => kern c Y τ ξ * ((ω.1 τ : ℂˣ) : ℂ)⁻¹ * ((ideleModule F τ : ℝ) : ℂ)) (ideleMeasure F) →
    ∫ p, coefK c Y (tau p.1 p.2) ξ * wt ω p.1 p.2 ∂(muE F) =
      ∫ τ, kern c Y τ ξ * ((ω.1 τ : ℂˣ) : ℂ)⁻¹ * ((ideleModule F τ : ℝ) : ℂ) ∂ideleMeasure F

def SLocal : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∃ C₀ : ℂ, C₀ ≠ 0 ∧ ∀ (y : (UpperTheory.V.TR.Rinf F)ˣ), (∀ v, 0 < y.val v) → ∀ (yf : (Af F)ˣ) (ξ : Fˣ),
    Integrable (fun τ : IdeleGroup F => kern c (yAd y yf) τ ξ * ((ω.1 τ : ℂˣ) : ℂ)⁻¹ * ((ideleModule F τ : ℝ) : ℂ))
      (ideleMeasure F) ∧
    ∫ τ, kern c (yAd y yf) τ ξ * ((ω.1 τ : ℂˣ) : ℂ)⁻¹ * ((ideleModule F τ : ℝ) : ℂ) ∂ideleMeasure F =
      C₀ * if ∀ v, 0 < reAt v (ξ : F) then
        coefAt (divS ω c) (algebraMap F (Af F) (ξ : F) * (yf : Af F)) *
          Complex.exp (-(2 * Real.pi : ℂ) * ∑ v, (reAt v (ξ : F) : ℂ) * (y.val v : ℂ))
      else 0

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
