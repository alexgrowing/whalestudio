import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrystallineCocycles
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTateTwistDualPerfectPairingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1DualPairStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoExactAnnihilatorsPeriodDatum
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTop
import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTopEuler
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

namespace GlobalTheory.HyodoFin

theorem finite_continuous_cocycles_localGaloisRep : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V]
    [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V]
    [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V),
    (∀ v, Continuous fun g => ρ g v) → Module.Finite ℚ_[l] ↥(continuousCocycles ρ) := by
  intro l _ P K V _ _ _ _ _ _ _ ρ hc
  obtain ⟨ρ', m, hc', hD⟩ := GlobalTheory.T.exists_tateTwistDual_perfectPairing l P K V ρ hc
  letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let A : GRep ↥(GK K) ℚ_[l] ℚ_[l] ℤ_[l] := { V := V, ρ := ρ, cont := hc }
  let A' : GRep ↥(GK K) ℚ_[l] ℚ_[l] ℤ_[l] :=
    { V := Fin (finrank ℚ_[l] V) → ℚ_[l], ρ := ρ', cont := hc' }
  have hH := (GlobalTheory.T.finrank_H1_dual_pair CompanionTheory.LocalTateOrthogonality.Gcoh.top_tate CompanionTheory.LocalTateOrthogonality.Gcoh.top_euler l P K ℚ_[l] ℤ_[l]
    GlobalTheory.Published.BlochKato.goodO_padicInt A A' m hD).1
  exact GlobalTheory.BlochKatoAnn.finite_continuous_cocycles_localGaloisRep A hH

end GlobalTheory.HyodoFin
