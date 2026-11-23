import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeaklyRegularOfCotangentIndep
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weakly_regular_of_cotangent_indep : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] (d : ℕ) (a : Fin d → R), ringKrullDim R ≤ d → LinearIndependent (ResidueField R) (fun j : {j : Fin d // a j ∈ maximalIdeal R} => ((maximalIdeal R).toCotangent ⟨_, j.2⟩ : CotangentSpace R)) → RingTheory.Sequence.IsWeaklyRegular R (List.ofFn a) ∧ Module.length R (R ⧸ Ideal.span (Set.range a)) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.RegSeq.isWeaklyRegular_and_length_quotient_le_one | exact GlobalTheory.CompanionTheory.RegSeq.isWeaklyRegular_and_length_quotient_le_one | (intros; apply GlobalTheory.CompanionTheory.RegSeq.isWeaklyRegular_and_length_quotient_le_one <;> assumption)
