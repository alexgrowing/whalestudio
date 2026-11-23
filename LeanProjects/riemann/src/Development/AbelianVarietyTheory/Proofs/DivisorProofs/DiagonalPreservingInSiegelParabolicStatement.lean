import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalPreservingInSiegelParabolic
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupIsoGLStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralKeepsDoublingDiagonalAdicCompletio
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubledUnitaryChartSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasIwasawaDecompositionDoubledSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormCmExtensionSplitPlaceEqZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAndIwasawaOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhere
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
open Formalism.UG (IsUnifV qV)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_preserving_in_siegel_parabolic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (X₂ : Spc F E (n + n)), J.det ≠ 0 → X₂.J = dblGram finSumFinEquiv J → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (p : UA σ X₂.J), p ∈ UAt σ X₂ (evFin F v) → KeepsDiag finSumFinEquiv ((mat p).map (piW t)) → p ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype := by
  first | exact @GlobalTheory.ThK.SplitSiegel.mem_siegel_of_split | exact GlobalTheory.ThK.SplitSiegel.mem_siegel_of_split | (intros; apply GlobalTheory.ThK.SplitSiegel.mem_siegel_of_split <;> assumption)
