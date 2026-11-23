import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CmHeckeCharacterInfinityType
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousIdeleCircle
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_hecke_character_infinity_type : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (χ : HChar E) (hu : IsUnitary χ) (n : I → ℤ), Formalism.L2.Host.HChar.HasInf χ φ n → ∀ i : I, (toHecke χ hu).infiniteTau (InfinitePlace.mk (φ i)) = 0 ∧ ((toHecke χ hu).infiniteWeight (InfinitePlace.mk (φ i))).natAbs = (n i).natAbs := by
  first | exact @GlobalTheory.CompanionTheory.HeckeArch.infiniteParams_of_hasInf | exact GlobalTheory.CompanionTheory.HeckeArch.infiniteParams_of_hasInf | (intros; apply GlobalTheory.CompanionTheory.HeckeArch.infiniteParams_of_hasInf <;> assumption)
