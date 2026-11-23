import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FoundBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

namespace UpperTheory.ConvolutionTheory.Dr

structure Carries {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ} (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (π : TR.CuspSub E n) (V : Submodule ℂ (LL μ)) : Prop where
  summand : IsSummand μ V
  carrier_eq : Fb.carrier π = formsIn μ V

def ExCusp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (V : Submodule ℂ (LL μ)), IsSummand μ V → ∃! π : TR.CuspSub E n, Carries μ π V

def ExSummand : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (π : TR.CuspSub E n) (V : Submodule ℂ (LL μ)),
    Carries μ π V ↔ Fb.carrier π ≤ centralCuspForms E n ∧ V = ((Fb.carrier π).map (clsL μ)).topologicalClosure

def ExTwist : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (π : TR.CuspSub E n), 1 ≤ n → ∃ χ : Formalism.L2.Host.HChar E,
      (∃ s : ℂ, ∀ x, ((χ.1 x : ℂˣ) : ℂ) = (((GroundTheory.Global.IdeleGroup.ideleModule E x).1 : ℝ) : ℂ) ^ s) ∧
      ∃ V, Carries μ (π.twist χ) V

def LocEmb : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (π : TR.CuspSub E n) (V : Submodule ℂ (LL μ)) (h : Carries μ π V), ∃ J : π.V →ₗ[ℂ] V, Function.Injective J ∧ DenseRange J ∧
      (∀ ψ : Fb.carrier π, (J (Fb.carrierEq π ψ)).1 = clsL μ ψ.1) ∧
      ∀ w g φ, J (π.locRep w g φ) = locOn h.summand w g (J φ)

def SatIff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (π : TR.CuspSub E n) (V : Submodule ℂ (LL μ)) (h : Carries μ π V) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ),
    (UpperTheory.CBC.Cusp.re π).sat w B ↔ GlobalTheory.LFun.HasSatGL w (locOn h.summand w) B

def SSatIff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (π : TR.CuspSub E n) (V : Submodule ℂ (LL μ)), Carries μ π V → ∀ (w : Pl E) (B : Multiset ℂ),
    SSat μ V w B ↔ ∃ B' : Multiset ℂˣ, B = B'.map (fun b : ℂˣ => (b : ℂ)) ∧ (UpperTheory.CBC.Cusp.re π).sat w B'

def LocFlath : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (π : TR.CuspSub E n)
    (D : AdelicDecomposition (Fb.toModule π)) (w : HeightOneSpectrum (𝓞 E)) σ,
    (UpperTheory.CBC.Cusp.re π).locComp w σ ↔ Nonempty (σ.ρ.Equiv (D.finite.π w))

def LocIff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (π : TR.CuspSub E n) (V : Submodule ℂ (LL μ)) (h : Carries μ π V) (w : HeightOneSpectrum (𝓞 E)) σ,
    (UpperTheory.CBC.Cusp.re π).locComp w σ ↔ ∃ f : σ.V →ₗ[ℂ] V, f ≠ 0 ∧ ∀ g x, f (σ.ρ g x) = locOn h.summand w g (f x)

def SelfTwIso : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (π : TR.CuspSub E n) (η : Formalism.L2.Host.HChar E),
    (∀ᶠ v : HeightOneSpectrum (𝓞 E) in Filter.cofinite, η.UnrAt v ∧ ∃ B, π.HasSat v B ∧ π.HasSat v (B.map (· * η.val v))) →
    (π.twist η).Iso π

end UpperTheory.ConvolutionTheory.Dr

end
