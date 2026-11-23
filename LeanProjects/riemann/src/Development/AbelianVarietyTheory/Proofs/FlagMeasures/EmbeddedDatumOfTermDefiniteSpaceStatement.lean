import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddedDatumOfTermDefiniteSpace
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AdaptSelf
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeddedDatum_of_term_definiteSpace : ∀ (K V W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (H : HermSpace K V) (HW : HermSpace K W) (e : W →ₗ[K] V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F G : FlagD H r) (𝔡 : Ideal (𝓞 K)) (N : NF H r) (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → IsEmb F HW e → Adapt F G 𝔡 N → N.IsTerm g Λ → IsDat HW g (lat0 F e Λ) r (N.gI g Λ) (datOf F G e g Λ) ∧ 1 ≤ N.gI g Λ ∧ (N.gI g Λ : ℝ) ≤ N.Del ∧ GlobalTheory.Mass.PD HW.B.flip ∧ Module.finrank K W + 2 * r + 1 = Module.finrank K V := by
  first | exact @GlobalTheory.DegAsm.isDat_datOf | exact GlobalTheory.DegAsm.isDat_datOf | (intros; apply GlobalTheory.DegAsm.isDat_datOf <;> assumption)
