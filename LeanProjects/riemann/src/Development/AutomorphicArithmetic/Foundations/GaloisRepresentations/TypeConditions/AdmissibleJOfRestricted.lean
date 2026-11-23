import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.DistinctAbsIrredConstituents
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.RhoBar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConclusionG5OfLocalDuality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleJOfParams
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DutiesOfLarge
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrreducibleDistinctConstituents

noncomputable section

namespace UpperTheory.GalS

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory GlobalTheory.StringRepresentationDecomposition UpperTheory.GalC

theorem g2g' {D : D7} (h : DeRhamJumpsDistinctCondition D) : ∀ i r, GoodR D.nd i r → (D.nd.l i = D.host.g 0 ∨ D.nd.l i = D.host.g 1) →
    ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ x, D.naut.IsdRW i (AdmissibleParameterJ.rQ D i r x) w ∧
      ∀ τ₀, InducesW D.nd i τ₀ w → D.naut.jumpsW i (AdmissibleParameterJ.rQ D i r x) τ₀ = D.naut.locAutHodgeTateWeightsLevelZero i τ₀ := h.1

theorem jc_of_u {D : D7} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))} (hr : GoodR D.nd i r)
    (hS : GlobalTheory.SplitCoef.OSplit D) (h : DistinctAbsIrredConstituents D.nd i r) : AbsIrreducibleDistinct D i r := by
  obtain ⟨K', hK', hA, _, hK⟩ := h
  exact GlobalTheory.T.absIrr_distinct_constituents_after_extension D i r (hS i) hr K' (algebraMap (Kf D.nd i) K') (fun x => (hK x).2)

end UpperTheory.GalS
