import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsContinuousLocalLift
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_local_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K), ∃ L : HA K σ J →* HA (AF F) σ J, Continuous L ∧ IsLift P σ J L := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.ExLift.exists_continuous_lift | exact GlobalTheory.CompanionTheory.SaGen.ExLift.exists_continuous_lift | (intros; apply GlobalTheory.CompanionTheory.SaGen.ExLift.exists_continuous_lift <;> assumption)
