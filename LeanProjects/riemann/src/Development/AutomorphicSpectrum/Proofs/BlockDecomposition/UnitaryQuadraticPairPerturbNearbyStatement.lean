import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryQuadraticPairPerturbNearby
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_quadratic_pair_perturb_nearby : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (a₀ b₀ : Fin M → K ⊗[F] E) (x : HA K σ J), IsQPairOf (sigR K σ) (JR K J) a₀ b₀ ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) → ∀ V ∈ nhds x, ∀ᶠ p in nhds (a₀, b₀), ∃ x' ∈ V, IsQPairOf (sigR K σ) (JR K J) p.1 p.2 ((HA.mat K σ J x').1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.NearPair.near_pair_main | exact GlobalTheory.CompanionTheory.SaGen.NearPair.near_pair_main | (intros; apply GlobalTheory.CompanionTheory.SaGen.NearPair.near_pair_main <;> assumption)
