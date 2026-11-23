import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticePreservedCofinitelyByUnit
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_preserved_cofinitely_by_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (y : (AF F ⊗[F] E)ˣ), ∀ᶠ v in cofinite, ∀ Y : Fin 1 → Fin 1 → Fv F v ⊗[F] E, (fun a i => cV v (y : AF F ⊗[F] E) * Y a i) ∈ latV b v ↔ Y ∈ latV b v := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitLat.eventually_cV_mul_mem_latV_iff | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitLat.eventually_cV_mul_mem_latV_iff | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitLat.eventually_cV_mul_mem_latV_iff <;> assumption)
