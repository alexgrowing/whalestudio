import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatConj
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.satContra :
    UpperTheory.Gal.TP.Loc.ContraUnit → UpperTheory.Gal.TP.Loc.SatContra := by
  intro hCU K _ _ w n V _ _ ρ hs hi hu B hB
  obtain ⟨-, C, hC⟩ := hCU (w.adicCompletion K) n V ρ hs hi hu
  obtain ⟨b, -, hp, hinv⟩ := hu
  refine UpperTheory.V.Af.Gk.satConj K n w V (smoothPart ρ.dual) ρ (contra ρ) b.flip C ?_ ?_ hC B hB
  · intro x hx
    by_contra h0
    have h1 := hp x h0
    have h2 : b x x = 0 := hx
    rw [h2] at h1
    simp at h1
  · intro g x y
    exact hinv g y x
