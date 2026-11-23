import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KaehlerRelationDerivationModIntegral
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_relation_derivationModIntegral : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (S : Subalgebra (O0 p) Ω), (∀ x ∈ S, IsInt p x) → (∀ x, ι x ∈ S) →
  ∀ D : Ω → Ω, IsDer S D → ∀ a b c x y z : On p n,
  a • KaehlerDifferential.D (O0 p) (On p n) x = b • KaehlerDifferential.D (O0 p) (On p n) y + c • KaehlerDifferential.D (O0 p) (On p n) z →
  IsInt p (ι a * D (ι x) - ι b * D (ι y) - ι c * D (ι z)) := by
  first | exact @GlobalTheory.KumDlog.kaehler_rel_isInt | exact GlobalTheory.KumDlog.kaehler_rel_isInt | (intros; apply GlobalTheory.KumDlog.kaehler_rel_isInt <;> assumption)
