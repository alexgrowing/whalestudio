import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V.Af.Bc

namespace UpperTheory.V.Af.Cr

def QuadCM : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (d : F) (δ : Ω),
    δ ^ 2 = algebraMap F Ω d → (∀ φ : F →+* ℝ, φ d < 0) →
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K) (_ : Algebra F K) (_ : Algebra K Ω) (_ : IsScalarTower F K Ω)
      (_ : IsAlgClosure K Ω), Module.finrank F K = 2 ∧ ∃ y : K, algebraMap K Ω y = δ ∧
        ∀ x : K, ∃ a b : F, x = algebraMap F K a + algebraMap F K b * y

def ImagGen : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 →
    ∃ (d : ℚ) (y : K), d < 0 ∧ y ^ 2 = (d : K) ∧ ∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * y

def IneRes : Prop :=
  ∀ (F₀ F Ω : Type) [Field F₀] [NumberField F₀] [Field F] [NumberField F] [Field Ω] [Algebra F₀ F] [Algebra F₀ Ω] [Algebra F Ω]
    [IsScalarTower F₀ F Ω] [IsAlgClosure F Ω], ∀ᶠ v : HeightOneSpectrum (𝓞 F₀) in Filter.cofinite,
      ∀ A : ValuationSubring Ω, IsPlaceOver A v → Ine (F := F₀) A ≤ (res F₀ Ω F).range

def ExQuadR : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime],
    l ≠ 2 → ∀ S : HeightOneSpectrum (𝓞 F) → Prop, (∀ᶠ v in Filter.cofinite, S v) →
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K) (_ : Algebra F K) (_ : Algebra K Ω) (_ : IsScalarTower F K Ω)
      (_ : IsAlgClosure K Ω), Module.finrank F K = 2 ∧
      (∀ (j : Ω →+* Om l) (L : FinExt l), (∀ x : F, j (algebraMap F Ω x) ∈ L.1) → ∀ x : K, j (algebraMap K Ω x) ∈ L.1) ∧
      ∃ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), S v ∧ IsPlaceOver A v ∧
        ∃ s ∈ Ine (F := F) A, s ∉ (res F Ω K).range

def NoTwistRam : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω]
    [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), Module.finrank F E = 2 →
    ∀ (n : ℕ), 1 ≤ n → ∀ (r : G F Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub F n), Continuous r → AttR ι r π →
      (∃ s, s ∉ (res F Ω E).range ∧ r s = 1) → ∀ η : HChar F, IsQuadCharOf E η → ¬ IsoTwist π η

def SSRes : Prop :=
  ∀ (Γ Γ' k : Type) [Group Γ] [Group Γ'] [Field k] (n : ℕ) (r : Γ →* GL (Fin n) k) (φ : Γ' →* Γ), φ.range.Normal →
    IsSSRep r → IsSSRep (r.comp φ)

def RealTransport : Prop :=
  ∀ (F K : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K] [IsCMField K] [Algebra F K],
    Module.finrank F K = 2 → ∀ χ : HChar F, ∃ χ' : HChar (maximalRealSubfield K),
      (∀ v' : InfinitePlace (maximalRealSubfield K), ∃ v : InfinitePlace F, χ'.locInf v' (-1) = χ.locInf v (-1)) ∧
      ∀ w : HeightOneSpectrum (𝓞 K), normV (w.under (𝓞 (maximalRealSubfield K))) = normV (w.under (𝓞 F)) ∧
        (χ.UnrAt (w.under (𝓞 F)) → χ'.UnrAt (w.under (𝓞 (maximalRealSubfield K))) ∧
          χ'.val (w.under (𝓞 (maximalRealSubfield K))) = χ.val (w.under (𝓞 F)))

def Parallel : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (χ : HChar F) (a : (F →+* ℂ) → ℤ), IsAlgPos χ a →
    ∀ φ φ', a φ = a φ'

def AlgOfSign : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (χ : HChar F) (b : ℤ), IsAlgPos χ (fun _ => b) →
    (∀ v : InfinitePlace F, χ.locInf v (-1) = (-1) ^ b) → χ.IsAlg fun _ => b

def CsdTw : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 1 ≤ n → ∀ (P : CuspSub K n) (χ : HChar (maximalRealSubfield K)),
    (CG.mk P).IsRegAlg → (∀ v v' : InfinitePlace (maximalRealSubfield K), χ.locInf v (-1) = χ.locInf v' (-1)) →
    GlobalTheory.ContraPair.DualIsConjBy P (compNorm K χ) →
    ∃ (κ : HChar K) (m : (K →+* ℂ) → ℤ), κ.IsAlg m ∧ GlobalTheory.ContraPair.DualIsConj (P.twist κ)

def BcDual : Prop :=
  GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.GelfandKazhdanDual →
  ∀ (F K : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K] [IsCMField K] [Algebra F K],
    Module.finrank F K = 2 → ∀ (n : ℕ), 1 ≤ n → ∀ (π : TR.CuspSub F n) (χ : HChar F) (P : CuspSub K n), π.Polarized χ → IsBC π P →
    ∃ χ' : HChar (maximalRealSubfield K), (∀ v v' : InfinitePlace (maximalRealSubfield K), χ'.locInf v (-1) = χ'.locInf v' (-1)) ∧
      GlobalTheory.ContraPair.DualIsConjBy P (compNorm K χ')

end UpperTheory.V.Af.Cr
