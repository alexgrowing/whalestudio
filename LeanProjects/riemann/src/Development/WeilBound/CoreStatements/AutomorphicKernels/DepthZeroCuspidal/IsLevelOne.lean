import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Whittaker

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsLevelOne (ψ : AddChar k Circle) : Prop := ∃ c : kˣ, HasConductor ψ c ∧ ord k c = 1

def PTau {m : ℕ} (ψ' : AddChar k Circle) (τ : IrrRep (GL (Fin m) k)) : Prop :=
  (∃ ω : kˣ →* ℂˣ, HasCentralChar τ.ρ ω) ∧
    ∃ v' ∈ fixed τ.ρ (KOne k (Fin m)), ∃ l' : Module.Dual ℂ τ.V, IsFunctional ψ' τ.ρ l' ∧ l' v' ≠ 0

end Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def unrPar (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (μ : {μ : (w.adicCompletion E)ˣ →* ℂˣ // IsUnram μ}) : WD h :=
  WD.lpOfChar h (μ.1.comp a) (ha.smooth (isSmoothChar_of_isUnram μ.2))

end PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

end
