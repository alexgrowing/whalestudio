import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnitScalingLatticeMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsContent
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_unit_scaling_lattice_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m' : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (c : Fv F v ⊗[F] E) (a : ℝ≥0), IsUnit c → c ∈ intK b v → (coordK (Fv F v) b lam).map (fun x => c * x) = a • coordK (Fv F v) b lam → ∀ y ∈ primV σ J b v, ∃ g : HA (Fv F v) σ (hypOne J), actW (Fv F v) σ (hypOne J) g (e0 _ M) = scalT c y ∧ stageInt (Fv F v) σ J b lam m' ((latV b v).indicator 1) g = (a : ℝ≥0∞) ^ n * m' (latV b v) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypMass.StageVal.stageInt_primV | exact GlobalTheory.CompanionTheory.WeilSiegel.HypMass.StageVal.stageInt_primV | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypMass.StageVal.stageInt_primV <;> assumption)
