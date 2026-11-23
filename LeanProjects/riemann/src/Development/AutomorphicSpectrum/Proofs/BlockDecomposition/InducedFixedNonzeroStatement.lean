import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFixedNonzero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_fixed_nonzero : ∀ (G W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] (P : Subgroup G) (σ : Representation ℂ P W) (K : Subgroup G), IsOpen (K : Set G) → ∀ x : W, x ≠ 0 → (∀ p : P, (p : G) ∈ K → σ p x = x) → fixed (smInd P σ) K ≠ ⊥ := by
  first | exact @GlobalTheory.CompanionTheory.SmInd.fixed_smInd_ne_bot_of_fixed | exact GlobalTheory.CompanionTheory.SmInd.fixed_smInd_ne_bot_of_fixed | (intros; apply GlobalTheory.CompanionTheory.SmInd.fixed_smInd_ne_bot_of_fixed <;> assumption)
