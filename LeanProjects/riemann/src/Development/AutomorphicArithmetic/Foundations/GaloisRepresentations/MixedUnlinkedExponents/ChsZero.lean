import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.Gal.GamX

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def chs (s : Multiset (IrrGL k)) : Multiset (kˣ →* ℂˣ) :=
  s.filterMap fun y => if h : ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ then some h.choose else none

def vals (c : Multiset (kˣ →* ℂˣ)) (θ : kˣ →* ℂˣ) : Multiset ℂˣ :=
  (c.filter fun ξ => IsUnram (ξ * θ)).map fun ξ => (ξ * θ) (unif k)

theorem chs_zero : chs (0 : Multiset (IrrGL k)) = 0 := rfl

end Loc

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] {v : HeightOneSpectrum (𝓞 K)}

def Thru (w : PlacesOver L v) (ζ : (w.1.adicCompletion L)ˣ →* ℂˣ) : Prop :=
  ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ, IsSmoothChar χ ∧ IsUnram (ζ * χ.comp (nm w))

def up (w : PlacesOver L v) (s : Multiset (IrrGL (v.adicCompletion K))) : Multiset ((w.1.adicCompletion L)ˣ →* ℂˣ) :=
  (chs s).map fun ξ => ξ.comp (nm w)

def GamSum : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [IsTotallyComplex L] [Algebra K L]
    [IsGalois K L], (Module.finrank K L).Prime → ∀ n : ℕ, 2 ≤ n → ∀ (π : CuspSub K n) (P : CuspSub L n),
    WeakBC (CG.mk π).HasSat (CG.mk P).HasSat →
    ∀ (v : HeightOneSpectrum (𝓞 K)) s (s' : ∀ w : PlacesOver L v, Multiset (IrrGL (w.1.adicCompletion L))),
      SuppAt π v s → (∀ w, SuppAt P w.1 (s' w)) → ∀ θ : (v.adicCompletion K)ˣ →* ℂˣ, IsSmoothChar θ →
      ∑ w, vals (chs (s' w)) (θ.comp (nm w)) = ∑ w : PlacesOver L v, vals (up w s) (θ.comp (nm w))

def GamOne : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [IsTotallyComplex L] [Algebra K L]
    [IsGalois K L], (Module.finrank K L).Prime → ∀ n : ℕ, 2 ≤ n → ∀ (π : CuspSub K n) (P : CuspSub L n),
    WeakBC (CG.mk π).HasSat (CG.mk P).HasSat →
    ∀ (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v), (∀ u : PlacesOver L v, u = w) →
      ∀ s s', SuppAt π v s → SuppAt P w.1 s' → (chs s').filter (Thru w) = up w s

def GamMixed : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [IsTotallyComplex L] [Algebra K L]
    [IsGalois K L], (Module.finrank K L).Prime → ∀ n : ℕ, 1 ≤ n → ∀ (π : CuspSub K n) (P : CuspSub L n),
    WeakBC (CG.mk π).HasSat (CG.mk P).HasSat →
    ∀ (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v) s s', SuppAt π v s → SuppAt P w.1 s' →
      (chs s').filter (Thru w) = up w s

end UpperTheory.Gal.GamX
