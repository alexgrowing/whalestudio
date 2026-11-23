import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Hilbert
import GroundTheory.GlobalFields.TateThesis.GlobalZetaSplit
import GroundTheory.GlobalFields.TateThesis.SchwartzBruhatDual

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

structure Hyp (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) : Prop where
  fin : IsOfFinOrder ω
  odd : ∀ v, ω.locInf v (-1) = -1
  cond : ∀ w, IsCondAt w ω (c w)
  ram : ∃ w, c w ≠ 0

def arch (x y : UpperTheory.V.TR.Rinf F) : ℂ :=
  ∏ v, (((x v : ℂ) + Complex.I * (y v : ℂ)) * Complex.exp (-(Real.pi : ℂ) * ((x v : ℂ) ^ 2 + (y v : ℂ) ^ 2)))

def dd (w : HeightOneSpectrum (𝓞 F)) : ℤ := (ordI w (differentIdeal ℤ (𝓞 F)) : ℤ)

open Classical in

def Phi (c : HeightOneSpectrum (𝓞 F) → ℕ) (ξ : Fin 2 → Ad F) : ℂ :=
  arch (UpperTheory.V.TR.pInf F (ξ 0)) (UpperTheory.V.TR.pInf F (ξ 1)) *
    if ∀ w, Valued.v (pLoc F w (pFin F (ξ 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧
        Valued.v (pLoc F w (pFin F (ξ 1)) - 1) ≤ WithZero.exp (-(c w : ℤ)) then 1 else 0

open Classical in

def PhiH (c : HeightOneSpectrum (𝓞 F) → ℕ) (ξ : Fin 2 → Ad F) : ℂ :=
  arch (UpperTheory.V.TR.pInf F (ξ 0)) (UpperTheory.V.TR.pInf F (ξ 1)) *
    if ∀ w, Valued.v (pLoc F w (pFin F (ξ 0))) ≤ WithZero.exp ((c w : ℤ) + dd w) ∧
        Valued.v (pLoc F w (pFin F (ξ 1))) ≤ WithZero.exp ((c w : ℤ) + dd w)
    then ((finiteAdelicChar F (pFin F (ξ 1)) : Circle) : ℂ) else 0

def rowA (ξ : Fin 2 → F) : Fin 2 → Ad F := fun i => algebraMap F (Ad F) (ξ i)

def thetaS (Ψ : (Fin 2 → Ad F) → ℂ) (h : GA F 2) : ℂ :=
  ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, Ψ (rowA ξ.1 ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F)))

def thetaT (Ψ : (Fin 2 → Ad F) → ℂ) (h : GA F 2) : ℂ :=
  ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, Ψ (((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ.1)

def absD (g : GA F 2) : ℝ := (IdeleGroup.ideleModule F (Matrix.GeneralLinearGroup.det g) : ℝ)

def w0 (F : Type) [Field F] [NumberField F] : InfinitePlace F := Classical.arbitrary _

def eisInt (ω : HChar F) (Ψ : (Fin 2 → Ad F) → ℂ) (g : GA F 2) (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) : ℂ :=
  thetaS Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) * g) *
    ((ω.1 (moduleSection (w0 F) t * (u : Ideles F)) : ℂˣ) : ℂ)⁻¹ * ((t : ℝ) : ℂ) * ((absD g ^ ((1 : ℝ) / 2) : ℝ) : ℂ)

def Eis (ω : HChar F) (Ψ : (Fin 2 → Ad F) → ℂ) (g : GA F 2) : ℂ :=
  ∫ t, ∫ u in normOneFundamentalDomain F, eisInt ω Ψ g t u ∂normOneMeasure F ∂posRealMeasure

def SPois : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∃ C : ℂ, ∀ h : GA F 2,
    Summable (fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} => ‖Phi c (rowA ξ.1 ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F)))‖) ∧
    Summable (fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} => ‖PhiH c (((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ.1)‖) ∧
    thetaS (Phi c) h = C * ((absD h)⁻¹ : ℝ) * thetaT (PhiH c) h

def SInt : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∀ g : GA F 2, Integrable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F => eisInt ω (Phi c) g p.1 p.2)
    (posRealMeasure.prod ((normOneMeasure F).restrict (normOneFundamentalDomain F)))

def SGrowth : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∀ g : GA F 2, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖Eis ω (Phi c) (g * UpperTheory.V.TR.infGL F 2 y)‖ ≤ C * UpperTheory.V.TR.height y ^ N

def SSmooth : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → Eis ω (Phi c) ∈ UpperTheory.V.TR.Sm F 2

def SLeft : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  ∀ γ g, Eis ω (Phi c) (ratGL F 2 γ * g) = Eis ω (Phi c) g

def SLevel : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∀ w, ∀ k ∈ K1 w (c w), ∀ g, Eis ω (Phi c) (g * finGL F 2 (locGL F 2 w k)) = Eis ω (Phi c) g

def SOpen : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∀ hs : Eis ω (Phi c) ∈ UpperTheory.V.TR.Sm F 2,
    IsOpen {k | UpperTheory.V.TR.finRep F 2 k ⟨Eis ω (Phi c), hs⟩ = ⟨Eis ω (Phi c), hs⟩}

def SCent : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∀ (z : Ideles F) (g : GA F 2),
    Eis ω (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * Eis ω (Phi c) g

def SKfin : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∀ hs : Eis ω (Phi c) ∈ UpperTheory.V.TR.Sm F 2,
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => UpperTheory.V.TR.cptRep F 2 k ⟨Eis ω (Phi c), hs⟩))

def SWt : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∀ hs : Eis ω (Phi c) ∈ UpperTheory.V.TR.Sm F 2, ∀ v,
    UpperTheory.V.TR.Eop v 0 1 ⟨Eis ω (Phi c), hs⟩ - UpperTheory.V.TR.Eop v 1 0 ⟨Eis ω (Phi c), hs⟩ =
      (Complex.I * (1 : ℕ)) • (⟨Eis ω (Phi c), hs⟩ : UpperTheory.V.TR.Sm F 2)

def SLow : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∀ hs : Eis ω (Phi c) ∈ UpperTheory.V.TR.Sm F 2, ∀ v,
    UpperTheory.V.TR.Eop v 0 0 ⟨Eis ω (Phi c), hs⟩ - UpperTheory.V.TR.Eop v 1 1 ⟨Eis ω (Phi c), hs⟩ =
      Complex.I • (UpperTheory.V.TR.Eop v 0 1 ⟨Eis ω (Phi c), hs⟩ + UpperTheory.V.TR.Eop v 1 0 ⟨Eis ω (Phi c), hs⟩)

def SZfin : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  IsOfFinOrder ω → ∀ φ : UpperTheory.V.TR.Sm F 2,
    (∀ (z : Ideles F) (g : GA F 2), φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g) →
    (∀ v, UpperTheory.V.TR.Eop v 0 1 φ - UpperTheory.V.TR.Eop v 1 0 φ = (Complex.I * (1 : ℕ)) • φ) →
    (∀ v, UpperTheory.V.TR.Eop v 0 0 φ - UpperTheory.V.TR.Eop v 1 1 φ = Complex.I • (UpperTheory.V.TR.Eop v 0 1 φ + UpperTheory.V.TR.Eop v 1 0 φ)) →
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (UpperTheory.V.TR.Sm F 2) => z φ) '' UpperTheory.V.TR.Zalg F 2))

def SExp : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∃ C₀ L : ℂ, C₀ ≠ 0 ∧
    HasExp (Eis ω (Phi c)) 1 (fun _ => L) fun 𝔪 => C₀ * ∑ᶠ 𝔯 ∈ {𝔯 | 𝔯 ∣ 𝔪}, chiI ω c 𝔯

def SSmul : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ)
  (k : ℕ) (φ : UpperTheory.V.TR.Sm F 2) (a : ℂ), a ≠ 0 →
    (IsHol k c ω φ → IsHol k c ω (a • φ)) ∧
    ∀ (c₀ : (Af F)ˣ → ℂ) (b : Ideal (𝓞 F) → ℂ), HasExp φ.1 k c₀ b → HasExp (a • φ).1 k (fun y => a * c₀ y) fun 𝔪 => a * b 𝔪

end UpperTheory.HilbertEisensteinWeightOne
