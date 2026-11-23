import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralStrictlyDominantExists
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_strictly_dominant_exists : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∃ a : Levi k (Bl d), (∀ x : Levi k (Bl d), a * x = x * a) ∧ IsStrictlyDominant k N J d hd a ∧ ∀ U : Set (GL (Fin N) k), IsOpen U → (1 : GL (Fin N) k) ∈ U → ∃ j : ℕ, ∀ y ∈ KNl k N J d hd, (leviEmb k (stdBlocks d hd) a ^ j)⁻¹ * y * leviEmb k (stdBlocks d hd) a ^ j ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.CentralDom.exists_central_strictlyDominant | exact GlobalTheory.CompanionTheory.CentralDom.exists_central_strictlyDominant | (intros; apply GlobalTheory.CompanionTheory.CentralDom.exists_central_strictlyDominant <;> assumption)
