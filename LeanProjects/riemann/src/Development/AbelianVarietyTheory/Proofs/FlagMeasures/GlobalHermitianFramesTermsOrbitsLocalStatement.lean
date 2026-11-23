import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalHermitianFramesTermsOrbitsLocal
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalHermitianFrames_terms_orbits_local : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ d : G.Dat, (∃ Λ₀, G.IsTerm d Λ₀) → (∀ Λ : ∀ p, Submodule (A.L p).O (G.S p).V, (∀ p, (G.S p).IsTerm (d p) (Λ p)) → ∃ Γ, G.IsTerm d Γ ∧ ∀ p, ∃ h ∈ (G.S p).St, A.lat p Γ = h • Λ p) ∧ (∀ Γ Γ', G.IsTerm d Γ → Submodule.IsLattice E Γ' → (G.LRel Γ Γ' ↔ ∀ p, ∃ h ∈ (G.S p).St, A.lat p Γ' = h • A.lat p Γ)) ∧ Equivalence G.LRel ∧ Equivalence G.DRel := by
  first | exact @GlobalTheory.HL.GlobalOrbits.global_terms_orbits | exact GlobalTheory.HL.GlobalOrbits.global_terms_orbits | (intros; apply GlobalTheory.HL.GlobalOrbits.global_terms_orbits <;> assumption)
