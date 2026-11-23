import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSelfDualFor

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

section Dual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def DualCl (x y : IrrGL k) : Prop :=
  ∃ (n : ℕ) (π π' : IrrRep (GL (Fin n) k)), x = cls π ∧ y = cls π' ∧ Nonempty (π'.ρ.Equiv (contra π.ρ))

def SegDual (Δ Δ' : Segment k) : Prop :=
  Δ'.len = Δ.len ∧ DualCl (Δ.first.nu ((Δ.len : ℂ) - 1)) Δ'.first

end Dual

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

structure CuspLaws (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (r : IrrGL (w.adicCompletion E) → WD h) : Prop where

  bij : Set.BijOn r {x | x.IsCusp} {y | IsIrrWD y}

  dim : ∀ x, x.IsCusp → (r x).lpDim = x.1

  twist : ∀ x, x.IsCusp → ∀ χ hχ, r (x.tw χ hχ) = (r x).lpTwist (χ.comp a) (ha.smooth hχ)

  central : ∀ x : IrrGL (w.adicCompletion E), x.IsCusp → ∀ ω, HasCentralChar x.rep ω →
    ∀ σ, ((r x).eig σ).prod = (ω (a σ) : ℂ)

  dual : ∀ x y, x.IsCusp → y.IsCusp → DualCl x y → r y = (r x).lpDual

  eps : ∀ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ → ψ ≠ 1 →
    ∀ x y : IrrGL (w.adicCompletion E), x.IsCusp → y.IsCusp → y.1 < x.1 →
      HasPairGamma ψ x.rep y.rep (e ψ ((r x).lpChar (r y)))

def IsLExt (r rc : IrrGL (w.adicCompletion E) → WD h) : Prop :=
  ∀ (l : List (Segment (w.adicCompletion E))) (x : IrrGL (w.adicCompletion E)),
    IsL (l : Multiset (Segment (w.adicCompletion E))) x.rep → rc x = segSum r l

end GlobalTheory.LocLanglands

end
