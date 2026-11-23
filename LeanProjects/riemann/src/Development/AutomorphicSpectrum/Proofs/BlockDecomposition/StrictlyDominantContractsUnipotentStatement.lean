import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictlyDominantContractsUnipotent
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictly_dominant_contracts_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ t : Levi k (Bl d), IsStrictlyDominant k N J d hd t → ∀ n ∈ unipRad k (stdBlocks d hd), ∃ r : ℕ, leviEmb k (stdBlocks d hd) t ^ r * n * (leviEmb k (stdBlocks d hd) t ^ r)⁻¹ ∈ KN k N J d hd := by
  first | exact @GlobalTheory.CompanionTheory.ExpandN.exists_pow_conj_mem_KN | exact GlobalTheory.CompanionTheory.ExpandN.exists_pow_conj_mem_KN | (intros; apply GlobalTheory.CompanionTheory.ExpandN.exists_pow_conj_mem_KN <;> assumption)
