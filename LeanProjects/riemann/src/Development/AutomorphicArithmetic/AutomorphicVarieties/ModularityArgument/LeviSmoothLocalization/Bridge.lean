import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL
open UpperTheory.Zero.LLC UpperTheory.V.Z.Gam GroundTheory.Global.SemiLocal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

def PlainIff : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub K n) v,
    (∀ σ, π.IsLocComp v σ → GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred)) ↔
      TorAt π v ∧ ∀ s, SuppAt π v s → Unl (Ideal.absNorm v.asIdeal) s

def WinOfP : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 1 ≤ n → ∀ π : CuspSub K n, ∃ t : ℝ, ∀ v,
    ((∀ σ, π.IsLocComp v σ → GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred)) → WinAt π t v) ∧
      ∀ B, (CG.mk π).HasSat v B → WinAt π t v

def SuppSmo1 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (π π' : CuspSub K 1),
    (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ∃ B, (CG.mk π).HasSat v B ∧ (CG.mk π').HasSat v B) →
    ∀ (t : ℝ) v, WinAt π t v → WinAt π' t v

theorem winOfP_of (hp : PlainIff) (h : WinOf) (hs : SphUnl) : WinOfP := by
  intro K _ _ _ n hn π
  obtain ⟨t, ht⟩ := h K n hn π
  exact ⟨t, fun v => ⟨fun a => ht v ((hp K n hn π v).1 a).1 ((hp K n hn π v).1 a).2,
    fun B hB => ht v (hs K n hn π v B hB).1 (hs K n hn π v B hB).2⟩⟩

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
