import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicMemPartialFlag
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimal_parabolic_mem_partial_flag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X : Matrix (Fin n) (Fin r) E), ∀ p ∈ minParOne σ J X, ∀ s : Fin r, p ∈ GlobalTheory.UAut.parFlag σ J (pre X s) fun _ => 0 := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.mem_parFlag_first_of_minParOne | exact GlobalTheory.CompanionTheory.RapidDecay.mem_parFlag_first_of_minParOne | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.mem_parFlag_first_of_minParOne <;> assumption)
