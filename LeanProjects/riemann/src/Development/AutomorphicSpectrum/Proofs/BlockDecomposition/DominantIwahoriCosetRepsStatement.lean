import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantIwahoriCosetReps
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_iwahori_coset_reps : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ t : Levi k (Bl d), IsDominant k N J d hd t → ∃ r : ℕ, 0 < r ∧ ∃ x : Fin r → GL (Fin N) k, (∀ i, x i ∈ KN k N J d hd) ∧ ∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ J ⊓ J.map (MulAut.conj (leviEmb k (stdBlocks d hd) t)).toMonoidHom := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.exists_fin_KN_coset_reps | exact GlobalTheory.CompanionTheory.Casselman.exists_fin_KN_coset_reps | (intros; apply GlobalTheory.CompanionTheory.Casselman.exists_fin_KN_coset_reps <;> assumption)
