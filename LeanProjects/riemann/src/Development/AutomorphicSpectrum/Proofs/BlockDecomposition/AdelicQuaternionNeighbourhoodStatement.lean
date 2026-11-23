import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicQuaternionNeighbourhood
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_quaternion_neighbourhood : ∀ {F : Type} [Field F] [NumberField F] (d β : F) (a : Q d β (AF F)), ∀ V ∈ 𝓝 a,
  ∃ T : Finset (Pl F), ∃ U : (u : Pl F) → Set (Q d β (Kp u)),
    (∀ u, U u ∈ 𝓝 (qmap (proj u) a)) ∧ (∀ w : InfinitePlace F, (Sum.inl w : Pl F) ∈ T) ∧
    ∀ b : Q d β (AF F), (∀ u ∈ T, qmap (proj u) b ∈ U u) →
      (∀ v : HeightOneSpectrum (𝓞 F), (Sum.inr v : Pl F) ∉ T → IntQ v (qmap (proj (Sum.inr v)) b)) → b ∈ V := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.Box.basic_nhd | exact GlobalTheory.CompanionTheory.PlaneSA.Box.basic_nhd | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.Box.basic_nhd <;> assumption)
