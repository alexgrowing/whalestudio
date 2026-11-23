import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlagTransitiveOfBase
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_transitive_of_base : ∀ {R : Type} [CommRing R] (c : R →+* R) (𝔬 : Subring R), IsHermRing c 𝔬 → HasBase c 𝔬 → FlagTransitive c 𝔬 := by
  first | exact @GlobalTheory.CompanionTheory.KFin.Flag.flagTransitive | exact GlobalTheory.CompanionTheory.KFin.Flag.flagTransitive | (intros; apply GlobalTheory.CompanionTheory.KFin.Flag.flagTransitive <;> assumption)
