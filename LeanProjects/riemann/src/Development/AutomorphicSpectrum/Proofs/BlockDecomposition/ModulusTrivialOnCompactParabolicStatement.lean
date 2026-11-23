import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusTrivialOnCompactParabolic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_trivial_on_compact_parabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b n : ℕ) (e : Fin a ⊕ Fin b ≃ Fin n) (K : Subgroup (GL (Fin n) k)), IsCompact (K : Set (GL (Fin n) k)) → ∀ p : parab k (two e), (p : GL (Fin n) k) ∈ K → deltaHalf k (Two (Fin a) (Fin b)) (leviProj k (two e) p) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.ModCompactParab.deltaHalf_leviProj_eq_one_of_isCompact | exact GlobalTheory.CompanionTheory.ModCompactParab.deltaHalf_leviProj_eq_one_of_isCompact | (intros; apply GlobalTheory.CompanionTheory.ModCompactParab.deltaHalf_leviProj_eq_one_of_isCompact <;> assumption)
