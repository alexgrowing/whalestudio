import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.ZDecompAt

theorem zDecomp_of_cheb : GlobalTheory.TwSys.Cheb → ∀ (D : D7), GlobalTheory.BlockComplement.GaloisRepsCusp D →
    ∀ i : D.nd.Loc, ZDecomp D.nd i := by
  intro hC D hG i π hπ r hr
  obtain ⟨ρ, hρ⟩ := GlobalTheory.BlockComplement.complement_at hC D hG i π hπ r hr
  obtain ⟨e, he⟩ := hρ.rho
  exact ⟨ρ, e, fun g u => he g u⟩

end GlobalTheory.ZDecompAt
