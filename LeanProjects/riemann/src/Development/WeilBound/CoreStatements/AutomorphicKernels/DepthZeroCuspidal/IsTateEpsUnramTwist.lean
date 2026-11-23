import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.IsLevelOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BrauerDegreeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneInductionPrincipleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedRepresentationCharacterStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneOfFiniteImageStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultiplicativeVirtualCharacterStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalExtensionOfFiniteIndexWeilSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupRestriction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSumTwistCompat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Whittaker

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Loc

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

section WDLemmas

theorem lpOfChar_lpTwist {p q r : Weil h →* ℂˣ} (hp : GlobalTheory.WeilDeligne.IsSmooth p)
    (hq : GlobalTheory.WeilDeligne.IsSmooth q) (hr : GlobalTheory.WeilDeligne.IsSmooth r) (e : ∀ σ, p σ * q σ = r σ) :
    (WD.lpOfChar h p hp).lpTwist q hq = WD.lpOfChar h r hr := by
  rw [WD.lpOfChar, WD.lpTwist_mk, WD.lpOfChar]
  refine WD.sound ⟨LinearEquiv.refl ℂ _, fun σ v => ?_, fun v => rfl⟩
  funext i
  simp only [LinearEquiv.refl_apply, WDRep.twist_ρ, WDRep.ofChars_ρ, LinearMap.smul_apply, Pi.smul_apply,
    diagEnd_apply, smul_eq_mul, ← e σ, Units.val_mul]
  ring

end WDLemmas

def TwPow (ε : EpsFamily A) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (ψ : AddChar (w.adicCompletion E) Circle) (ϖ : (w.adicCompletion E)ˣ) (x : WD h) : Prop :=
  ∃ j : ℤ, ∀ χ : {μ : (w.adicCompletion E)ˣ →* ℂˣ // IsUnram μ},
    ε E w h ψ (x.lpTwist (χ.1.comp a) (ha.smooth (isSmoothChar_of_isUnram χ.2))) = χ.1 ϖ ^ j * ε E w h ψ x

end PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

end
