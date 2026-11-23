import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterValuesInjectiveLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointObjectsTransportAlongConjugationOverFractioStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointGaloisRepsConjugateOverFractionFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplementOfCharactersUniqueUpToConjStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.ConsEveryFamilyWild

theorem main : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r₀ : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ₀ : N.X i → (GE N →* GL (Fin R.r) (N.O i))), GoodR N i r₀ → TakenWild N i r₀ ρ₀ → ∀ (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))), GoodR N i r → ∀ π ∈ N.Z i, (∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := R.t) (r π) (ρ π) (N.chi i) e) → ∃ S : IdempotentChoiceData N i, GoodCongruenceObjects N r ρ π S ∧ IsWildInertiaCyclotomicElement N i S.g0 := by
  intro hC R H what₂ N i r₀ ρ₀ h₀ hT r ρ hr π hπ hd
  obtain ⟨A, a1, a2, a3, a4, a5, a6, a7, TA, repA, ρA, χA, hE, hS, hCh⟩ := hT
  obtain ⟨g0, L, eB, e1, X0, hg, hch, hroots⟩ := hCh π hπ
  obtain ⟨S₀, hg0, -, -, -, hS₀⟩ := (GlobalTheory.ConsExists.consExist N i r₀ ρ₀ A TA repA ρA χA
    (fun x => (h₀ x).1) hE hS).2.2 π hπ g0 L eB e1 X0 hg.1 hch hroots
  have hconj := GlobalTheory.T.pointGaloisReps_conjugate_over_fraction_field hC N i r₀ r h₀ hr
  have hd₀ : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := R.t) (r₀ π) (ρ₀ π) (N.chi i) e := by
    refine ⟨S₀.e, fun g u => ?_⟩
    rw [GlobalTheory.ConsExists.overK_apply, GlobalTheory.ConsExists.overK_apply]
    exact hS₀.2.1 g u
  have hρ := GlobalTheory.T.complement_of_characters_unique_up_to_conj N i r₀ r ρ₀ ρ π (h₀ π).2.1 (hconj π) hd₀ hd
  obtain ⟨S, hSg, hS⟩ := GlobalTheory.T.pointObjects_transport_along_conjugation_over_fraction_field N i r₀ r ρ₀ ρ π hconj hρ S₀ hS₀
  exact ⟨S, hS, by rw [hSg, hg0]; exact hg⟩

end GlobalTheory.ConsEveryFamilyWild
