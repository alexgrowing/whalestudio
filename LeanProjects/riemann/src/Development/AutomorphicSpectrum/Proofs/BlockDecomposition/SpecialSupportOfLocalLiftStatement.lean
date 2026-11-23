import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecialSupportOfLocalLift
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_support_of_local_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J), IsLift P σ J L → ∀ g ∈ SUSupp σ J (P.inj 1), ∃ x : HA K σ J, ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 ∧ L x = g := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.exists_lift_of_mem_supp | exact GlobalTheory.CompanionTheory.SaGen.exists_lift_of_mem_supp | (intros; apply GlobalTheory.CompanionTheory.SaGen.exists_lift_of_mem_supp <;> assumption)
