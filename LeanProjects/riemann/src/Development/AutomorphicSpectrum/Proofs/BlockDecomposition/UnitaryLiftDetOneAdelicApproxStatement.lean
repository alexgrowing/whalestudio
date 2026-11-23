import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLiftDetOneAdelicApprox
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lift_det_one_adelic_approx : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J), IsLift P σ J L → (∀ x : HA K σ J, ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 → L x ∈ SUSupp σ J (P.inj 1)) → ∀ ε : AF F, ε * P.inj 1 = P.inj 1 → ∀ a b : Fin M → E, IsoPlane K σ J (incV K a) (incV K b) → ¬ IsCompact (PlaneSupp σ J ε a b) := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.NotCompact.not_isCompact_planeSupp | exact GlobalTheory.CompanionTheory.SaGen.NotCompact.not_isCompact_planeSupp | (intros; apply GlobalTheory.CompanionTheory.SaGen.NotCompact.not_isCompact_planeSupp <;> assumption)
