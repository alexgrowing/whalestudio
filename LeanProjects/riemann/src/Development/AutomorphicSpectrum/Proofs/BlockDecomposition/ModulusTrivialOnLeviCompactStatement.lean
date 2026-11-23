import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusTrivialOnLeviCompact
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_trivial_on_levi_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsCompact (J : Set (GL (Fin N) k)) → ∀ x ∈ KM k N J d hd, deltaHalf k (Bl d) x = 1 := by
  first | exact @GlobalTheory.CompanionTheory.HalfModCompact.deltaHalf_eq_one_of_mem_KM | exact GlobalTheory.CompanionTheory.HalfModCompact.deltaHalf_eq_one_of_mem_KM | (intros; apply GlobalTheory.CompanionTheory.HalfModCompact.deltaHalf_eq_one_of_mem_KM <;> assumption)
