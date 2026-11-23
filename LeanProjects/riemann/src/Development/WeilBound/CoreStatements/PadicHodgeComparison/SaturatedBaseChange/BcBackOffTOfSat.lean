import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIntegralOpW
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DualIsConjOfIsCsd

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh GlobalTheory.LFun GlobalTheory.PRep Formalism.UG
open GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AutomorphicGaloisHodgeTate.SaturatedBaseChange

def CompUnique : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (U : Submodule ℂ (UA E n → ℂ)), IsAutRepU U →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ σ τ : LocIrr w n,
      IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ →
      IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → Nonempty (σ.ρ.Equiv τ.ρ)

def CuspOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) (n c : ℕ), 1 ≤ n →
    ∀ (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (ρ : ∀ i, LocIrr w (a i)) (σ : ∀ i, LocIrr w (d i * a i)),
      (∀ i, 1 ≤ a i ∧ 1 ≤ d i) →
      (∀ i, GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i).ρ (ρ i).smooth (ρ i).irred) (d i) (σ i).ρ) →
      (locProd h w σ).IsIrreducible → IsCuspidal (locProd h w σ) → c = 1 ∧ ∀ i, d i = 1

def OneFactor : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (h : ∑ _i : Fin 1, 1 * n = n) (ρ : LocIrr w n) (σ : Fin 1 → LocIrr w (1 * n)),
      GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of ρ.ρ ρ.smooth ρ.irred) 1 (σ 0).ρ →
      Nonempty ((locProd (N := fun _ : Fin 1 => 1 * n) h w σ).Equiv ρ.ρ)

end PositivityTheory.AutomorphicGaloisHodgeTate.SaturatedBaseChange

end
