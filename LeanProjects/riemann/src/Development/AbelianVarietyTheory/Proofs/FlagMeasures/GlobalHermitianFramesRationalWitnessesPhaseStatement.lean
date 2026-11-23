import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalHermitianFramesRationalWitnessesPhase
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalHermitianFrames_rational_witnesses_phase : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ d Λ, G.IsTerm d Λ → (∃ n ∈ G.N, ∃ n' ∈ G.N', ∀ p m m', A.Ext p n m → A.Ext p n' m' → (G.S p).IsTermW (d p) (A.lat p Λ) m m') ∧ ∀ m m' : ∀ p, (G.S p).GLV, (∀ p, (G.S p).IsTermW (d p) (A.lat p Λ) (m p) (m' p)) → G.om d Λ = ∏ᶠ p, (G.S p).psi (m p) * ((G.S p).psi' (m' p))⁻¹ := by
  first | exact @GlobalTheory.HL.GlobalWit.global_witnesses | exact GlobalTheory.HL.GlobalWit.global_witnesses | (intros; apply GlobalTheory.HL.GlobalWit.global_witnesses <;> assumption)
