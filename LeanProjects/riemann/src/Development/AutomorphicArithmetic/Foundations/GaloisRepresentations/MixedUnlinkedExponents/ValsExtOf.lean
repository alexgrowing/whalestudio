import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ChsZero

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.Gal.GamX

def lp (A : Multiset ℂˣ) : ℂ[X] := (A.map fun a => 1 - C ((a : ℂˣ) : ℂ) * X).prod

def LpInj : Prop := ∀ A B : Multiset ℂˣ, lp A = lp B → A = B

def LpPow : Prop := ∀ (f : ℕ), 0 < f → ∀ A B : Multiset ℂˣ, lp A = (lp B).comp (X ^ f) → A.map (· ^ f) = f • B

def ChsFacts : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s : Multiset (IrrGL k)),
    (∀ ξ, ξ ∈ chs s ↔ ξ ∈ chars s) ∧ (∀ ξ ∈ chs s, IsSmoothChar ξ) ∧ ∀ θ : kˣ →* ℂˣ, pol s θ = lp (vals (chs s) θ)

def ValsExt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (c c' : Multiset (kˣ →* ℂˣ)) (θ : kˣ →* ℂˣ), vals c θ = vals c' θ →
    (c.filter fun ξ => IsUnram (ξ * θ)) = c'.filter fun ξ => IsUnram (ξ * θ)

def FdegEq : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)), Nonempty (PlacesOver L v) ∧ ∀ w w' : PlacesOver L v, fdeg w = fdeg w'

def TwVals : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (d f : ℕ)
    (e : ℕ → ((v.adicCompletion K)ˣ →* ℂˣ)), (∀ w : PlacesOver L v, fdeg w = f) → Nonempty (PlacesOver L v) →
    (∀ (j : ℕ) (w : PlacesOver L v), (e j).comp (nm w) = 1) →
    (∀ (w w' : PlacesOver L v) (μ : (v.adicCompletion K)ˣ →* ℂˣ), IsUnram (μ.comp (nm w)) → IsUnram (μ.comp (nm w'))) →
    (∀ (w : PlacesOver L v) (μ : (v.adicCompletion K)ˣ →* ℂˣ), IsSmoothChar μ → IsUnram (μ.comp (nm w)) →
      ((Finset.range d).filter fun j => IsUnram (μ * e j)).card = ∑ w' : PlacesOver L v, fdeg w') →
    ∀ (c : Multiset ((v.adicCompletion K)ˣ →* ℂˣ)), (∀ ξ ∈ c, IsSmoothChar ξ) → ∀ θ : (v.adicCompletion K)ˣ →* ℂˣ, IsSmoothChar θ →
      (∑ j ∈ Finset.range d, vals c (θ * e j)).map (· ^ f) =
        f • ∑ w : PlacesOver L v, vals (c.map fun ξ => ξ.comp (nm w)) (θ.comp (nm w))

def LpPowOf : Prop := LpInj → LpPow
def ValsExtOf : Prop := PolFacts → ValsExt
def TwValsOf : Prop := NormVal → TwVals
def GamSumOf : Prop := MatchBCX → NormCnt → NormVal → LpPow → ChsFacts → FdegEq → TwVals → GamSum
def GamOneOf : Prop := ChsFacts → ValsExt → GamSum → GamOne

end UpperTheory.Gal.GamX
