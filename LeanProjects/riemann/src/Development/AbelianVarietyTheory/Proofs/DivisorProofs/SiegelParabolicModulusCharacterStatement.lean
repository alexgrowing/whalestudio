import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicModulusCharacter
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
theorem _root_.GlobalTheory.T.siegel_parabolic_modulus_character : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (X₂ : Spc F E (n + n)), J.det ≠ 0 → X₂.J = dblGram finSumFinEquiv J → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (p : UA σ X₂.J), p ∈ UAt σ X₂ (evFin F v) → ∀ hp : p ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype, ((absE F E (aOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype ⟨p, hp⟩) : ℝ≥0) : ℝ) = (qV F v : ℝ) ^ (-(Formalism.UG.ordL (leviMat finSumFinEquiv ((mat p).map (piW t))).det - Formalism.UG.ordL (quotMat finSumFinEquiv ((mat p).map (piW t))).det)) := by
  first | exact @GlobalTheory.ThK.SiegelAbs.absE_aOf | exact GlobalTheory.ThK.SiegelAbs.absE_aOf | (intros; apply GlobalTheory.ThK.SiegelAbs.absE_aOf <;> assumption)
