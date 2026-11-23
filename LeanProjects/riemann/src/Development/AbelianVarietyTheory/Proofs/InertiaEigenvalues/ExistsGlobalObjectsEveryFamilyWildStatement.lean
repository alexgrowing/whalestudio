import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalObjectsEveryFamilyWild
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_globalObjects_every_family_wild : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r₀ : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ₀ : N.X i → (GE N →* GL (Fin R.r) (N.O i))), GoodR N i r₀ → TakenWild N i r₀ ρ₀ → ∀ (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))), GoodR N i r → ∀ π ∈ N.Z i, (∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := R.t) (r π) (ρ π) (N.chi i) e) → ∃ S : IdempotentChoiceData N i, GoodCongruenceObjects N r ρ π S ∧ IsWildInertiaCyclotomicElement N i S.g0 := by
  first | exact @GlobalTheory.ConsEveryFamilyWild.main | exact GlobalTheory.ConsEveryFamilyWild.main | (intros; apply GlobalTheory.ConsEveryFamilyWild.main <;> assumption)
